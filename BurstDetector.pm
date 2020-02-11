package BurstDetector;

# Copyright 2015-2016 Niklas Edmundsson <nikke@acc.umu.se>
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
#     Unless required by applicable law or agreed to in writing, software
#     distributed under the License is distributed on an "AS IS" BASIS,
#     WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#     See the License for the specific language governing permissions and
#     limitations under the License.

# Hacked by nikke as part of a Master Thesis project in spring 2015.
#
# This module implements file burst detection using a simple threshold based
# detector and naïve seasonal forecasting to predict the baseline bandwidth.
# The first file burst detection threshold is set based on the forecast and
# standard deviation (ie. forecast accuracy), exceeding this is reported as
# burstfactor 1. The configured maxbw is used as a base for further
# burstfactors, 2 exceeds maxbw, 3 exceeds maxbw*2 etc.

# Bandwidth is estimated as a moving average over timeslotsize*avgslots
# seconds, 20*180 => 1 hour.


use warnings;
use strict;

use Exporter;
use vars qw(@ISA @EXPORT_OK);
@ISA         = qw(Exporter);
@EXPORT_OK   = ();

use Carp;
use JSON;
use Statistics::Basic qw(:all);
use Statistics::Descriptive;

my %config_keys = (
	maxbw => 'Max target bandwidth, bytes/s',
	targetfactor => 'Target burst threshold factor, float',
	filefactor => 'File burst threshold factor, float',
	pretrigfactor => 'File pre-trigger factor, float',
	filetrigslots => 'Need this many consecutive time slots fullfilling the trigger condition before trigger happens',
	minfileimpact => 'Lower limit on files to track, bytes/s',
	minbwhist => 'Ignore historical values lower than this, bytes/s',
	timeslotsize => 'Size of time slots',
	timeslotlag => 'Max age of records to consider',
	avgslots => 'Number of timeslots for averaging',
	historyslotsize => 'Averaging period (computed: timeslotsize*avgslots)',
	historymaxage => 'Max age of history to keep (computed)',
	forecast_valuecount => 'Values considered for forecast',
	forecast_maxscope => 'How many weeks/days/hours back to consider',
	debugprintfunc => 'Function to use when printing debug messages',
);

my %config = (
	default => {
		maxbw		=> 100000000,
		targetfactor	=> 4, # 4 s.d. =~ 99.997% quantile
		filefactor	=> 3, # 3 s.d. =~ 99.9% quantile
		pretrigfactor	=> 1, # 1 s.d. =~ 68% quantile
		filetrigslots	=> 2, # 1 up to avgslots
		minfileimpact	=> 5000,
		minbwhist	=> 5000000,
		timeslotsize	=> 20,
		timeslotlag	=> 20,
		avgslots	=> 180,
		forecast_valuecount => 3,
		forecast_maxscope => 5,
		debugprintfunc => \&debugprint_default,
	},
);

# Let these be fixed for now
my $forecast_daylen = 60*60*24;
my $forecast_weeklen = $forecast_daylen*7;

my $timeslotsize;
my $timeslotlag;
my $avgslots;

my %offloads;
my %forecasts;
my %residuals;
my %burstfiles;
my $histref = {};
my $initdone = 0;
my $currtimeslot = 0;
my $pasttimeslot = 0;


# --------------------------------------
# Functions below are to be called from the outside.

# Perform init functions for this module.
sub init
{
	$timeslotsize = $config{default}{timeslotsize};
	$timeslotlag = $config{default}{timeslotlag};
	$avgslots = $config{default}{avgslots};

	if($timeslotlag%$timeslotsize != 0) {
		confess("Config error: timeslotlag not multiple of timeslotsize");
	}

	$config{default}{historyslotsize} = $timeslotsize * $avgslots;

	$config{default}{historymaxage} = $forecast_weeklen * ($config{default}{forecast_maxscope}+1);

	foreach my $v ($forecast_daylen, $forecast_weeklen) {
		if($v%$config{default}{historyslotsize} != 0) {
			confess "Config error: historyslotsize $config{default}{historyslotsize} not multiple of $v (day/week)";
		}
	}

	if($config{default}{timeslotlag} >= $config{default}{historyslotsize}) {
		confess("Config error: timeslotlag > historyslotsize");
	}

	$initdone=1;
}


# Returns the history slot for a given time.
sub historyslot($)
{
	my $time = shift;

	if(!$initdone) {
		croak "Must call init first";
	}

	confess "time undef" unless(defined($time));

	return(int($time) - int($time)%($config{default}{historyslotsize}));
}


# Returns the time slot for the given time.
sub timeslot($)
{
	my $time = shift;

	if(!$initdone) {
		croak "Must call init first";
	}

	return(int($time) - int($time)%$timeslotsize);
}


# Register an offload event for processing.
# Returns an array with bursfactor=file values.
# burstfactor > 0 indicates a detected (increase in) burst.
# burstfactor == 0 indicates that the file isn't considered a burst anymore.
sub reg_offload($$$$)
{
	my $time = shift;
	my $target = shift;
	my $size = shift;
	my $file = shift;

	if(!$initdone) {
		croak "Must call init first";
	}

	my $timeslot = timeslot($time);
	my $histslot = historyslot($time);

	my @ret;
	if(!$currtimeslot) {
		$currtimeslot = $timeslot;
	}
	if($currtimeslot != $timeslot) {
		if(!$pasttimeslot) {
			$pasttimeslot = $currtimeslot;
		}
		$currtimeslot = $timeslot;
	}

	if($timeslot < $pasttimeslot) {
		debugprint("ERROR: Ignoring data from time $time older than pasttimeslot $pasttimeslot\n");
		return @ret;
	}
	# FIXME: Assumes timeslotlag is lower than historyslotsize
	while($pasttimeslot && $pasttimeslot < $currtimeslot - $timeslotlag) {
		collapse_timeslot($pasttimeslot);
		push @ret, analyze_bursts($pasttimeslot);
		push @ret, analyze_timeslot($pasttimeslot);
		my $prevhs = historyslot($pasttimeslot);
		$pasttimeslot += $timeslotsize;
		if($prevhs != historyslot($pasttimeslot)) {
			reg_histslot($histref, $prevhs);
		}
	}

	if($target) {
		handle_forecast($histref, $histslot, $target);
	}

	if($target && $size && $file) {
		$offloads{$target}{$timeslot}{amount} += $size;
		$offloads{$target}{$timeslot}{$file} += $size;
	}

	return @ret;
}


##############################################################################
# Functions below are to be considered internal to this module.


# Default debug message print function.
sub debugprint_default
{
	print @_;
}


# Prints a debug message.
sub debugprint
{
	&{$config{default}{debugprintfunc}}(@_);
}


# Set config value for target/default key.
sub set_config
{
	my ($target, $key, $value) = @_;

	if($initdone) {
		croak "Can't change config after init()";
	}

	if(!$config_keys{$key}) {
		croak "Undefined config key $key";
	}

	$config{$target}{$key} = $value;
}


# Get config value matching target/default key.
sub get_config
{
	my ($target, $key) = @_;

	if(defined($config{$target}) && defined($config{$target}{$key})) {
		return $config{$target}{$key};
	}
	if(defined($config{default}) && defined($config{default}{$key})) {
		return $config{default}{$key};
	}

	confess "No default config found for $key";
}


# Analyzes detected bursts, if they are even more popular or if the popularity
# has faded so we can remove them from the list.
sub analyze_bursts($)
{
	my $timeslot = shift;

	my $histslot = historyslot($timeslot);

	my @ret;

	return @ret if(scalar(keys %burstfiles) == 0);

	foreach my $target (keys %offloads) {
		next unless(defined($residuals{$target}));

		my $stddev = $residuals{$target}->standard_deviation();
		my $maxbw = get_config($target, 'maxbw');
		if($stddev) {
			$maxbw += int($stddev)*get_config($target, 'targetfactor');
		}
		foreach my $file (keys %burstfiles) {
			next unless(defined($offloads{$target}{$file}));
			my $fval = int(mean($offloads{$target}{$file})/$timeslotsize);
			if($fval > $maxbw * ($burstfiles{$file}{burstfactor}+1)) {

				push @{$burstfiles{$file}{times}}, $timeslot;
				$burstfiles{$file}{burstfactor} ++;
				debugprint "BURST($burstfiles{$file}{burstfactor}) on $target at $timeslot: fval $fval B/s maxbw $maxbw B/s file $file\n";
				push @ret, $file, $burstfiles{$file}{burstfactor};
			}
		}
	}
	
	if($timeslot == historyslot($timeslot)) {
		# Only do more expensive cleanup periodically
		FILE:
		foreach my $file (keys %burstfiles) {
			my $fsum = 0;
			foreach my $target(keys %offloads) {
				next unless(defined($offloads{$target}{$file}));
				my $fval = int(mean($offloads{$target}{$file})/$timeslotsize);
				$fsum += $fval;

				# Keep files with rates higher than the
				# threshold at the time of detection.
				next FILE if($fval > $burstfiles{$file}{detectthres});
				debugprint "NOBURST candidate: $target $file $fval B/s\n";
			}
			# Never remove burst state unless file total is below
			# detection threshold.
			next if ($fsum > $burstfiles{$file}{detectthres});
			debugprint "NOBURST detected at $timeslot: unburst $file\n";
			delete $burstfiles{$file};
			push @ret, $file, 0;
		}
	}

	return @ret;
}


# Given two Statistics::Basic::Vector objects, subtract decrement from vector.
sub subtract_vector
{
	my ($vector, $decrement) = @_;

	my @v = $vector->query();
	my @d = $decrement->query();

	if(scalar(@v) != scalar(@d)) {
		confess "vector and decrement have diffferent size";
	}

	for(my $i=0; $i <= $#v; $i++) {
		my $e = $v[$i] - $d[$i];
		if($e >= 0) {
			$v[$i] = $e;
		}
	}

	$vector->insert(@v);
}


# Analyze timeslot (but really checks history slot) for bursts and new files
# causing them.
sub analyze_timeslot($)
{
	my $timeslot = shift;

	my $histslot = historyslot($timeslot);

	my @ret;

	foreach my $target (keys %offloads) {
		next unless(defined($residuals{$target}));
		next unless(defined($offloads{$target}{avgvec}));

		my $stddev = $residuals{$target}->standard_deviation();
		my $tthres;
		my $fthres;
		my $fprethres;
		my $maxbw = get_config($target, 'maxbw');
		if($stddev && $forecasts{$histslot}{$target}) {
			$tthres = $forecasts{$histslot}{$target}+int($stddev)*get_config($target, 'targetfactor');
			$fthres = $forecasts{$histslot}{$target}+int($stddev)*get_config($target, 'filefactor');
			$fprethres = $forecasts{$histslot}{$target}+int($stddev)*get_config($target, 'pretrigfactor');
			$maxbw += int($stddev)*get_config($target, 'targetfactor');
		}
		if(!$tthres || $tthres > $maxbw) {
			$tthres = $maxbw;
		}
		if(!$fthres || $fthres > $maxbw) {
			$fthres = $maxbw;
		}
		my $tval = int(mean($offloads{$target}{avgvec})/$timeslotsize);

		next if($tval < $tthres);
		debugprint "Examining $target for file burst candidates at $timeslot: val $tval B/s tthres $tthres B/s\n";
		foreach my $file(keys %{$offloads{$target}}) {
			next unless($file =~ /^\//); # skip non-files
			next if(defined($burstfiles{$file}));
			# Allow configuring the number of consecutive timeslots
			# needed to even consider a file as a burst candidate.
			# This is to avoid one download of a huge file to
			# register as a burst.
			my $slotsactive = 0;
			foreach my $otf (reverse $offloads{$target}{$file}->query()) {
				if($otf) {
					$slotsactive++;
				}
				else {
					last;
				}
			}
			next unless($slotsactive >= get_config($target, 'filetrigslots'));
			my $fval = int(mean($offloads{$target}{$file})/$timeslotsize);
			if($fval >= $fthres) {
				push @{$burstfiles{$file}{times}}, $timeslot;
				$burstfiles{$file}{burstfactor} = 1;
				$burstfiles{$file}{detectrate} = $fval;
				$burstfiles{$file}{detectthres} = $fthres;
				debugprint "BURST($burstfiles{$file}{burstfactor}) on $target at $timeslot: fval $fval B/s fthres $fthres B/s file $file\n";
				push @ret, $file, $burstfiles{$file}{burstfactor};
				# Remove the rate caused by this file from the total
				subtract_vector($offloads{$target}{avgvec}, $offloads{$target}{$file});
			}
			elsif($fprethres && $fval >= $fprethres) {
				my $nextbf=1;
				if($burstfiles{$file}) {
					$nextbf += $burstfiles{$file}{burstfactor};
				}
				debugprint "BURST(P$nextbf) on $target at $timeslot: fval $fval B/s fprethres $fprethres B/s file $file\n";
				push @ret, $file, "P$nextbf";
			}
		}
	}

	return @ret;
}


# Collapses a time slot:
# - Add bandwidth for time slot to matching history slot.
# - Keep stats only for files with transfer rate impact more than minimpact
# - Remove time slot.
sub collapse_timeslot($)
{
	my $timeslot = shift;

	my $doclean = 0; # Only do more expensive cleanup periodically
	if($timeslot == historyslot($timeslot)) {
		$doclean = 1;
	}

	foreach my $target (keys %offloads) {
		if(!defined($offloads{$target}{avgvec})) {
			$offloads{$target}{avgvec} = vector();
			$offloads{$target}{avgvec}->set_size($avgslots);
		}
		if(!defined($offloads{$target}{$timeslot})) {
			# Register 0 transfers in this timeslot before moving on
			$offloads{$target}{avgvec}->insert(0);
			# Add 0 transfers for files not seen in this timeslot
			foreach my $file(keys %{$offloads{$target}}) {
				next unless($file =~ /^\//); # skip non-files
				$offloads{$target}{$file}->insert(0);
			}
			next;
		}
		my $minfileimpact = get_config($target, 'minfileimpact');
		my $tsamount = $offloads{$target}{$timeslot}{amount};
		delete $offloads{$target}{$timeslot}{amount};
		foreach my $file(keys %{$offloads{$target}{$timeslot}}) {
			if(!defined($offloads{$target}{$file})) {
				next if($offloads{$target}{$timeslot}{$file}/($timeslotsize*$avgslots) < $minfileimpact);
				$offloads{$target}{$file} = vector();
				$offloads{$target}{$file}->set_size($avgslots);
			}
			$offloads{$target}{$file}->insert($offloads{$target}{$timeslot}{$file});
			if(defined($burstfiles{$file})) {
				# Don't include known burst-files in the
				# timeslot total rate.
				$tsamount -= $offloads{$target}{$timeslot}{$file};
			}
		}
		# Add 0 transfers for files not seen in this timeslot
		foreach my $file(keys %{$offloads{$target}}) {
			next if(defined($offloads{$target}{$timeslot}{$file})); # skip seen
			next unless($file =~ /^\//); # skip non-files
			if($doclean && int(mean($offloads{$target}{$file})/$timeslotsize) < $minfileimpact) {
				delete $offloads{$target}{$file};
				next;
			}
			$offloads{$target}{$file}->insert(0);
		}
		if($tsamount < 0) {
			warn "BUG: $timeslot $target tsamount < 0";
			$tsamount = 0;
		}
		$offloads{$target}{avgvec}->insert($tsamount);
		delete $offloads{$target}{$timeslot};
	}
}


# Return a forecast for a given historyslot/target combo.
sub forecast($$$)
{
	my $histref = shift;
	my $predictslot = shift;
	my $target = shift;

	my $stat = Statistics::Descriptive::Full->new();

	my $minbw = get_config($target, 'minbwhist');

	# First try to find value up to $forecast_maxscope weeks back, then try
	# $forecast_maxscope days back. This is a seasonally naïve forecasting
	# method with the season length set to a week/day respectively.
	# Finally fall back to a truly naïve method: use the last observation.
	LOOP:
	foreach my $pass ($forecast_weeklen,$forecast_daylen,$config{default}{historyslotsize}) {
		foreach my $i (1 .. $config{default}{forecast_maxscope}) {
			my $hslot = $predictslot - $pass*$i;
			next unless(defined($histref->{$hslot}));
			next unless(defined($histref->{$hslot}{$target}));
			next if($histref->{$hslot}{$target} < $minbw);
			$stat->add_data($histref->{$hslot}{$target});
			last LOOP if($stat->count() >= $config{default}{forecast_valuecount});
		}
	}

	if($stat->count() > 0) {
#		debugprint "$predictslot $target forecast: ", $stat->median(),"\n";
		return $stat->median();
	}
	return 0;
}


# Attempts to create a forecast for a given target/historyslot combo if not
# attempted before. Records result in %forecasts hash.
sub handle_forecast($$$)
{
	my $histref = shift;
	my $predictslot = shift;
	my $target = shift;

	if(!defined($forecasts{$predictslot}) || !defined($forecasts{$predictslot}{$target})) {
		$forecasts{$predictslot}{$target} = forecast($histref, $predictslot, $target);
	}
}


# Register a new history slot with actual bandwidth.
sub reg_histslot($$)
{
	my $histref = shift;
	my $slot = shift;

	foreach my $t (keys %offloads) {
		# Don't stomp loaded history if valid
		if(!$histref->{$slot}{$t}) {
			$histref->{$slot}{$t} = int(mean($offloads{$t}{avgvec})/$timeslotsize);
		}

		handle_forecast($histref, $slot, $t);
		if(!defined($residuals{$t})) {
			$residuals{$t} = Statistics::Descriptive::Sparse->new();
		}
		if($forecasts{$slot}{$t}) {
			my $residual = $histref->{$slot}{$t} - $forecasts{$slot}{$t};
			$residuals{$t}->add_data($residual);
			debugprint "rate on $t at $slot-",$slot+$config{default}{historyslotsize}-1,": forecast: $forecasts{$slot}{$t} B/s actual: $histref->{$slot}{$t} B/s stddev: ",int($residuals{$t}->standard_deviation())," B/s\n";
		}
	}
}


# Load history from JSON file into $histref hash reference.
sub history_load($)
{
	my $jsonin = shift;

	if(open(my $rfh, '<', $jsonin)) {
		$histref = decode_json(<$rfh>);
		if(!close($rfh)) {
			carp "close $jsonin: $!";
			return 0;
		}
	}
	else {
		carp("open $jsonin: $!");
		return 0;
	}

	return 1;
}


# Save history from $histref hash reference to JSON file.
sub history_save($) {
	my $jsonout = shift;

	my $rc = 1;
	my $wfh;

	if(!$histref) {
		carp "No history to save";
		return 0;
	}

	# Remove expired values from history before saving
	my $maxage = time() - $config{default}{historymaxage};
	foreach my $t (keys %{$histref}) {
		next if($t >= $maxage);
		delete $histref->{$t};
	}

	if(!open($wfh, ">", "$jsonout.tmp")) {
		carp "open $jsonout.tmp: $!";
		return 0;
	}
	if(!print $wfh encode_json($histref)) {
		carp "print $jsonout.tmp: $!";
		$rc = 0;
	}
	if(!$wfh->flush()) {
		# Flush perl-buffered pending data.
		carp "flush $jsonout.tmp: $!";
		$rc = 0;
	}
	if(!$wfh->sync()) {
		# Force OS write to disk.
		carp "sync $jsonout.tmp: $!";
		$rc = 0;
	}
	if(!close($wfh)) {
		carp "close $jsonout.tmp: $!";
		$rc = 0;
	}
	if($rc) {
		if(!rename("$jsonout.tmp", $jsonout)) {
			carp "rename $jsonout.tmp $jsonout: $!";
			unlink("$jsonout.tmp");
			return 0;
		}
	}
	else {
		unlink("$jsonout.tmp");
		return 0;
	}

	return 1;
}

1;
