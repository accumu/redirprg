#!/usr/bin/perl
# vim:et:sts=4:sw=4:ai:

# Copyright 2007-2018 Niklas Edmundsson <nikke@acc.umu.se>
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

use strict;
use warnings;


# End of configuration
# ==========================================================================


# This Apache HTTPD RewriteMap program returns a target for redirection given
# a URI. For performance it's meant to be used with a SDBM map as a cache, so
# requests first query the SDBM map before doing a query to this program which
# caches the result in the map. This program takes care of all housekeeping
# of the SDBM.
#
# Idea of operation: Map all hosts onto a pie chart with $nbuckets positions,
# size scaled according to weight. When a host vanishes for some reason, the
# neighbouring hosts grows to accomodate the missing host. This preserves the
# uri->host mapping even if hosts are down. Hosts are selected by
# hashing the files device and inode (or the URI) into a value that fits into
# $nbuckets.
#
# Fixed redirects are handled by having a hash table containing the hash values
# of all fixed redirects, and we always check that table before doing ordinary
# dynamic redirect. Multihost fixed redirects are accomplished by rotating
# the fixed targets every $iterinterval second.
#
# Checking of host state is done by having a child that periodically does a
# HTTP HEAD request to all target hosts.
#
# On non-destination hosts, ie Frontends, an additional child is spawned that
# uses the BurstDetector module to determine access bursts to files and
# assign additional offloaders for those files.
#
# In order to be able to dynamically assign additional targets without
# real-time communication between Frontends and Offloaders each destination
# host accepts accesses for files with neighbour hosts as primary target,
# and Frontends assign neighbour hosts as secondary and third offload target
# if needed.

use Sys::Hostname;
use IO::Select;
use IO::Handle;
use Socket qw(:DEFAULT :addrinfo);
use LWP::UserAgent;
use HTTP::Request::Common;
use Digest::MD5 qw(md5_hex);
use Math::BigInt;
use Fcntl;   # For O_RDWR, O_CREAT, etc. used by SDBM_File
use SDBM_File;
use Fcntl;
use File::Tail;
use File::Basename;
use File::Path qw(make_path);
use POSIX qw(strftime);
use Time::HiRes;
use JSON;
use Getopt::Std;

# FIXME: Debug
#use Data::Dumper;
#$Data::Dumper::Sortkeys = 1;

# Find our own module in the same directory as this script.
use lib dirname (__FILE__);
use BurstDetector;

my $nbuckets        = 2147483647; # Should fit into 32bit signed, for safety.

my $hosts; # Ref to array of target hosts
my $fixed; # Ref to hash of fixed redirects
my $conf; # Ref to config hash
my $lastpurge;
my %myfqdn;
my %entries;
my %DB;
my $dbfilename=""; # The actual (main) DB file
my $dbentries = 0;
my %fixedhvals;
my %burstfiles;
my $iter = 0;
my $lastiter = time();
my $is_desthost = 0;
my $iterinterval;
my $logprogname = 'redirprg';
my %opts;

# $cfgmain file config items.
my %cfgmainitems = (
    ' PREAMBLE ' => {
        comment => 'redirprg.pl main configuration file. Loaded on startup only.',
    },
    loglevel => {
        desc => 'Minimum level of log messages to print, can be debug, notice or error.',
        default => 'debug',
        validre => '^(debug|notice|error)$',
    },
    domain => {
	desc => 'Domain name appended to all unqualified hostnames in config.',
	default => "ftp.example.com",
    },
    docroot => {
	desc => 'The true DocumentRoot.',
	default => "/srv/ftp",
    },
    dbfile => {
	desc => 'DBM file to store redirect entries in.',
	default => "/var/run/apache2.redirdb",
    },
    maxcache => {
	desc => 'Maximum number of redirect entries in memory cache.',
        default => "100000",
    },
    maxdb => {
	desc => 'Maximum number of redirect entries in DB.',
	default => "40000",
    },
    hitspromote => {
	desc => 'Min number of hits before promoting to DB.',
	default => "3",
    },
    maxhitage => {
	desc => 'Max time between hits (seconds).',
	default => "3600",
    },
    maxage => {
	desc => 'Maximum age of redirect entries (seconds).',
	default => "28800",
    },
    purgeinterval => {
	desc => 'How often purges of aged entries happen (seconds).',
	default => "1800",
    },
    checkuri => {
	desc => 'Default URI for host-up-checks.',
	default => "/",
    },
    remotecheckuri => {
	desc => 'Default URI to check for non-local targets, defined as name containing a dot.',
        default => "/",
    },
    checkinterval => {
	desc => 'Interval between host-up checks (seconds).',
        default => "30",
    },
    shorttimeout => {
	desc => 'Timeout if previous state was down (seconds).',
        default => "1",
    },
    longtimeout => {
	desc => 'Timeout if previous state was up (seconds).',
        default => "60",
    },
    iterintervalmin => {
	desc => 'How often to update fixed multihost redirects. Randomizes between min/max values (seconds).',
        default => "7",
    },
    iterintervalmax => {
	desc => 'How often to update fixed multihost redirects. Randomizes between min/max values (seconds).',
        default => "43",
    },
    minredirsize => {
	desc => "Don't redirect objects less than this size (bytes).",
        default => "4194304",
    },
    changinguris => {
	desc => "Regular Expression of URI:s whose inode can change without the name changes, meaning we must stat the file and check if it's changed. The RE is used with /i, ie case insensitive.",
        default => "current|latest|daily|weekly",
    },
    cfgcheckinterval => {
	desc => 'How often to check hosts and fixed redirect config files for changes (seconds).',
        default => "60",
    },
    offloadlogfile => {
	desc => 'Offload log file, used by BurstDetector. Passed through strftime().',
        default => "/var/log/fifologger/httpd-offload_%Y-%m-%d",
    },
    maxseenentries => {
	desc => 'Max number of ip:file tuples to track in order to filter out multiple hits generated by parallel downloads.',
        default => "50000",
    },
    minseenexpire => {
	desc => 'Min age of ip:file tuples to save (seconds). This just needs to be large enough to avoid double-counting the requests by download agents spawning multiple parallel downloads (seconds).',
        default => "60",
    },
    seenexpiresizefactor => {
	desc => 'Size factor for calculating the seenexpire, to cater for larger files taking longer time to download and thus might trigger more parallel downloads along the way.  Typically set to the average client download rate in bytes/s.',
        default => "10000000",
    },
    historyfile => {
	desc => 'File used for saving historic data used for burst detection.',
        default => "/var/spool/apache2/history.json"
    },
);

# $cfghosts per-host config items
my %cfghostsitems = (
    name => {
        desc => 'The (optionally short) name for the host. Unqualified names gets domain from the main config appended.',
    },
    checkuri => {
        desc => 'Optional check URI override for this host, default is to use remotecheckuri from the main config.',
    },
    weight => {
        desc => 'The amount of space the host should occupy in the pie-chart describing all targets. The sum is normalized to the entire pie-chart, so use whatever scale of numbers you fancy (but percent is easy to understand).',
    },
    maxbw => {
        desc => "The max estimated bandwidth to allow for this host. This is used by the frontends as a baseline for burst detection. Remember that it's an estimate, and that each frontend only sees its own traffic. (MB/s)",
    },
    comment => {
        desc => 'This is where you put your comment for your own use, commonly a host description.',
    },
    disabled => {
        desc => 'Whether the host is disabled or not. Can take either yes or no as value.',
        validre => '^(yes|no)$',
    },
);

# ------------------------------------------------------------------------

# Returns preamble for all log messages, styled to roughly match what
# Apache httpd 2.4+ prints in the error log.
sub logpreamble
{
    my $level = shift;
    $level = 'notice' unless($level);

    if($opts{t}) {
        return "$level: ";
    }

    my ($t, $us) = Time::HiRes::gettimeofday();
    $us = sprintf("%06d", $us);

    return strftime("[%a %b %d %T.$us %Y] [$logprogname:$level] [pid $$] ", localtime($t));
}


# Log debug entry, simply write to stderr and it lands in the httpd log.
sub debug {
    my @args = @_;

    return if($conf->{loglevel} ne 'debug');

    print STDERR logpreamble('debug'),@args;
}


# Log notice entry, simply write to stderr and it lands in the httpd log.
sub notice {
    my @args = @_;

    return if($conf->{loglevel} !~ /^(debug|notice)$/);

    print STDERR logpreamble('notice'),@args;
}


# Log error entry, simply write to stderr and it lands in the httpd log.
sub error {
    my @args = @_;

    print STDERR logpreamble('error'),@args;
}


# Read a simple JSON+comments config file, expects one data structure
# per file.
# Expects filename, returns reference.
sub readjsonconf {
    my ($file) = @_;
    my $fh;
    my $ref;

    if(!open($fh, '<', $file)) {
        error("Failed to load $file: $!\n");

        return undef;
    }

    # Read file and remove comments.
    my @cfg = grep(!/^\s*#/, (<$fh>));

    if(!close($fh)) {
        error("Error closing $file: $!\n");

        return undef;
    }

    eval {
        # join everything into one line and decode.
        # decode_json croaks on error, resulting in program exit on error.
        $ref = decode_json(join "", @cfg);
    };
    if($@) {
        error("Parsing $file failed: $@");

        return undef;
    }

    if(!$ref) {
        error("Parsed $file OK, but no resulting config object\n");

        return undef;
    }

    return $ref;
}


# Read main json-ish config file. It's simply a hash.
sub readmainconf {
    my ($file) = @_;
    my %cfg;

    my $fref = readjsonconf($file);

    if(!$fref) {
        return undef;
    }

    if(ref($fref) ne 'HASH') {
        error("config $file invalid - root object is not an hash\n");

        return undef;
    }

    # Copy defaults from the defined config items
    foreach my $k (keys %cfgmainitems) {
        $cfg{$k} = $cfgmainitems{$k}{default} if($cfgmainitems{$k}{default});
    }

    # Check if read config matches our expected config items and override
    # the defaults.
    foreach my $k (sort keys %{$fref}) {
        if(! $cfgmainitems{$k}) {
            error("config $file item $k is unknown\n");

            return undef;
        }
        if($cfgmainitems{$k}{validre}) {
            if($fref->{$k} !~ /$cfgmainitems{$k}{validre}/) {
                error("Parsed $file item $k value $fref->{$k} is invalid\n");

                return undef;
            }
        }
        $cfg{$k} = $fref->{$k};
    }

    return \%cfg;
}

# Read hosts json-ish config file. It's an array of per-host hashes.
sub readhostsconf {
    my ($file) = @_;
    my %cfg;

    my $fref = readjsonconf($file);

    if(!$fref) {
        return undef;
    }

    if(ref($fref) ne 'ARRAY') {
        error("config $file invalid - root object is not an array\n");

        return undef;
    }

    foreach my $h (@{$fref}) {
        if(ref($h) ne 'HASH') {
            error("config $file invalid - sub object is not a hash\n");

            return undef;
        }
        foreach my $k (keys %{$h}) {
            if(!$cfghostsitems{$k}) {
                error("Parsed $file item $k is unknown\n");

                return undef;
            }
            if($cfghostsitems{$k}{validre}) {
                if($h->{$k} !~ /$cfghostsitems{$k}{validre}/) {
                    error("Parsed $file item $k value $h->{$k} is invalid\n");

                    return undef;
                }
            }
        }
    }

    return $fref;

}

# Read fixed entries json-ish config file. It's a hash of filenames with
# a hosts subhash with an array of target hosts as value.
# This is overly elaborate, but the historical reason is this was originally
# hard-coded, and the rest of the code expects to add more items to the hash
# as the files are processed.
sub readfixedconf {
    my ($file) = @_;
    my %cfg;

    my $fref = readjsonconf($file);

    if(!$fref) {
        return undef;
    }

    if(ref($fref) ne 'HASH') {
        error("config $file invalid - root object is not a hash\n");

        return undef;
    }

    foreach my $f (keys %{$fref}) {
        if(ref($fref->{$f}) ne 'HASH') {
            error("config $file invalid - sub object $f is not a hash\n");

            return undef;
        }
        if(!$fref->{$f}{hosts}) {
            error("config $file invalid - sub object $f has no hosts child\n");

            return undef;
        }
        if(ref($fref->{$f}{hosts}) ne 'ARRAY') {
            error("config $file invalid - sub object $f hosts child is not an array\n");

            return undef;
        }
        if(!scalar(@{$fref->{$f}{hosts}})) {
            error("config $file invalid - sub object $f has empty hosts subarray\n");

            return undef;
        }
        if(scalar keys %{$fref->{$f}} > 1) {
            error("config $file invalid - sub object $f has no too many members\n");

            return undef;
        }
    }

    return $fref;
}

# Returns a random number between min and max.
sub random_interval($$)
{
    my $min = shift;
    my $max = shift;

    die "min $min must be < max $max" unless($min < $max);

    return $min + int(rand($max - $min));
}


# Returns values incrementing in the given steps, useful when you want to
# synchronize events across hosts
sub timestep
{
    my ($val, $step) = @_;

     return int($val/$step)*$step;
}


# Ties SDBM file $conf->{dbfile} to %DB hash.
sub tiedb
{
    my $createnew = shift;

    my $rwmode;
    if($createnew) {
        $rwmode = O_RDWR|O_CREAT|O_TRUNC;
    }
    else {
        $rwmode = O_RDWR;
    }
    if(!tie (%DB, 'SDBM_File', $conf->{dbfile}, $rwmode, 0644)) {
        warn "Couldn't open $conf->{dbfile} for writing: $!\n";
        return 0;
    }

    # SDBM is comprised of two files, so $conf->{dbfile} is just the basename.
    # This file is the one holding the data and growing large.
    $dbfilename = $conf->{dbfile} . SDBM_File::PAGFEXT;

    return 1;
}


# Unties %DB.
sub untiedb
{
    if(!untie %DB) {
        warn "Failed to close $conf->{dbfile}: $!\n";
        return 0;
    }

    return 1;
}


# Helper function to stay within the @hosts array.
sub wrap_pos($) {
    my $pos = shift;

    # Skip past fixed redirects
    while(defined($hosts->[$pos])) {
        if(!$hosts->[$pos]->{size} || !$hosts->[$pos]->{weight}) {
                $pos++;
                next;
        }
        last;
    }

    if($pos == -1) {
        return $#$hosts;
    }
    elsif($pos > $#$hosts) {
        return 0;
    }

    return $pos;
}


# Return the canonical name for a host.
sub getcanonnameandip($)
{
    my $name = shift;

    if($conf->{domain} && $name !~ /\./) {
    	$name .= ".$conf->{domain}";
    }

    # LWP barfs on IPv6 URLs, so force IPv4
    my ($err, @addrs) = getaddrinfo($name, undef, {flags=>AI_CANONNAME, family=>AF_INET});
    if($err) {
        warn "Error resolving $name: $err";
        return undef;
    }

    my $canonname = lc($addrs[0]->{canonname});

    my ($gnerr, $hostip) = getnameinfo($addrs[0]->{addr}, NI_NUMERICHOST, NIx_NOSERV);

    if($gnerr) {
        warn "Resolving $name: getnameinfo: $gnerr";
        return undef;
    }

    # For whenever LWP manages to handle v6 IP URLs again
    if($addrs[0]->{family} eq AF_INET6) {
        $hostip = "[$hostip]";
    }

    debug("Using $hostip to check status of $canonname ($name)\n");

    return ($canonname, $hostip);
}


# Resolve destination hosts and build the basic "pie chart".
sub resolve_desthosts() {
    my $totweight = 0;

    for(my $i=0; $i <= $#$hosts; $i++) {
        my ($fqdn, $hostip) = getcanonnameandip($hosts->[$i]->{name});

        unless($fqdn) {
            warn "host $hosts->[$i]->{name} not found, ignoring\n";
            next;
        }

        $hosts->[$i]->{fqdn} = $fqdn;
        $hosts->[$i]->{hostip} = $hostip;

        if($myfqdn{$fqdn}) {
            $is_desthost = 1;
            debug "$fqdn is configured as a destination host\n";
        }

        if(!$hosts->[$i]->{checkuri} && $hosts->[$i]->{name} =~ /\./) {
            $hosts->[$i]->{checkuri} = $conf->{remotecheckuri};
        }

        my $disabled = $hosts->[$i]->{disabled};
        unless($disabled && $disabled eq "yes") {
            $hosts->[$i]->{up} = 1;
        }

        # Fixed redirects.
        if(!$hosts->[$i]->{weight}) {
            next;
        }
        $totweight += $hosts->[$i]->{weight};
    }
    
    # Assign positions in the pie chart.
    my $chunksize = $nbuckets/$totweight;

    for(my $i=0; $i <= $#$hosts; $i++) {
        next unless $hosts->[$i]->{fqdn};
        next unless $hosts->[$i]->{weight};

        $hosts->[$i]->{size} = int($chunksize * $hosts->[$i]->{weight})+1;
    }

    my $currpos = 0;

    for(my $i=0; $i <= $#$hosts; $i++) {
        next unless $hosts->[$i]->{fqdn};
        next unless $hosts->[$i]->{weight};

        $hosts->[$i]->{middle} = $currpos;
        my $next = wrap_pos($i+1);
        $currpos += int($hosts->[$i]->{size}/2 + $hosts->[$next]->{size}/2);
    }
}


# Find my own fqdn
sub get_myfqdn() {
    my $n = hostname;
    $n =~ s/\..*$//;


    my $fqdn;
    
    while(1) {
        ($fqdn, undef) = getcanonnameandip($n);
        last if($fqdn);
        sleep 1;
    }

    $myfqdn{$fqdn} = 1;
    debug "myfqdn: $fqdn\n";
}


# Find a destination for this file.
# Argument: filename reference, hash value, file size (if available)
# Returns: Target hostname_filesize or _ if no redirect.
sub finddest
{
    my $quiet = shift;
    my $fileref = shift;
    my $hash = shift;
    my $size = shift;
    my $testiter = shift;
    my $destidx;

    if(!$testiter) {
        $testiter = $iter;
    }

    # Don't do redirect for non-existant files or small objects.
    if(!defined($size)) {
        return "_";
    }
    if($size < $conf->{minredirsize}) {
        return "_";
    }

    for(my $i=0; $i <= $#$hosts; $i++) {
        next unless($hosts->[$i]->{up});

        my $left = $hosts->[$i]->{left};
        my $right = $hosts->[$i]->{right};

        #debug "$i:$hosts->[$i]->{name}  l: $left  r: $right\n";

        if($left > $right) {
            # This occurs only for one host, the one in the "wrap-around".
            if($hash > $left || $hash < $right) {
                $destidx = $i;
                last;
            }
        }
        else {
            if($hash >= $left && $hash <= $right) {
                $destidx = $i;
                last;
            }
        }
    }

    if(!defined($destidx)) {
        # This should never happen
        debug "'${$fileref}' not redirected - no destination index found, this should not happen!\n" if(!$quiet);
        return "_";
    }


    if($is_desthost) {
        # Hosts defined as destination hosts, normally offload targets, also
        # accepts files with "neighbor" hosts as primary target. This is to
        # enable burst load handling by automatically offload popular files
        # to multiple offloaders.
        foreach my $closedest (wrap_pos($destidx-1), wrap_pos($destidx+1)) {
            if($myfqdn{$hosts->[$closedest]->{fqdn}}) {
                debug "'${$fileref}' not redirected - secondary destination target (destidx: $destidx  closedest: $closedest)\n" if(!$quiet);
                return "_";
            }
        }
    }

    if($burstfiles{${$fileref}}) {
        my @hostsup;
        push @hostsup, $destidx;
        foreach my $closedest (wrap_pos($destidx-1), wrap_pos($destidx+1)) {
            next unless($hosts->[$closedest]->{up});
            push @hostsup, $closedest;
            last if(scalar(@hostsup) > $burstfiles{${$fileref}}{burstfactor})
        }
        $destidx = $hostsup[$testiter % scalar(@hostsup)];
    }


    my $dest = $hosts->[$destidx]->{fqdn};
    if($dest && !$myfqdn{$dest}) {
        $size = "-" unless($size);
        return "${dest}_$size";
    }

    return "_";
}


# Calculate the positions the living hosts should occupy in the "pie chart"
sub calc_intervals() {
    # Figure out which interval the living hosts serve
    for(my $i=0; $i <= $#$hosts; $i++) {
        if(!$hosts->[$i]->{up}) {
            debug "Host $i:$hosts->[$i]->{name}  NOT UP\n";
            next;
        }
        if(!$hosts->[$i]->{weight}) {
            debug "Host $i:$hosts->[$i]->{name}  FIXED\n";
            next;
        }

        my $amt = $hosts->[$i]->{size}/2;
        my $next;
        for($next = wrap_pos($i+1); 
                !($hosts->[$next]->{up} && $hosts->[$next]->{weight}); 
                $next = wrap_pos($next+1))
        {
            if($hosts->[$next]->{size}) {
                $amt += $hosts->[$next]->{size};
            }
        }

        $amt += $hosts->[$next]->{size}/2;
        $amt = int($amt);
        # amt should now contain the amount between my middle and next's middle

        my $factor = $hosts->[$i]->{size} / ($hosts->[$i]->{size}+$hosts->[$next]->{size});
        my $myamt = int($amt * $factor);
        # myamt should be my part, scaled wrt my and nexts sizes.

        debug "Host $i:$hosts->[$i]->{name}  next=$next  size=$hosts->[$i]->{size} myamt=$myamt\n";

        $hosts->[$i]->{right} = ($hosts->[$i]->{middle} + $myamt) % $nbuckets;

        $hosts->[$next]->{left} = ($hosts->[$i]->{right} +1) % $nbuckets;
    }

    # Debug
    for(my $i=0; $i <= $#$hosts; $i++) {
        next unless $hosts->[$i]->{up};
        next unless $hosts->[$i]->{weight};
        my $r = $hosts->[$i]->{right};
        if($r < $hosts->[$i]->{left}) {
            $r += $nbuckets;
        }
        my $a = abs($r - $hosts->[$i]->{left});
        debug "Host $i:$hosts->[$i]->{name} weight: $hosts->[$i]->{weight} amount: $a middle: $hosts->[$i]->{middle} left: $hosts->[$i]->{left} right: $hosts->[$i]->{right}\n";
    }

    # Recalculate which host serves what
    if(!tiedb()) {
        return;
    }

    my($key,$ref);
    while (($key,$ref) = each %entries) {
        my $newdest = findfixed($ref->{hash}, $ref->{size});
        if(!$newdest) {
            $newdest = finddest(1, \$key, $ref->{hash}, $ref->{size});
        }
        if($newdest ne $ref->{val}) {
            debug "Change $key: $ref->{val} -> $newdest\n";
            $ref->{val} = $newdest;
            if($ref->{indb}) {
                eval {
                    $DB{$key} = $newdest;
                };
                if($@) {
                    error($@);
                    delete $DB{$key}; # Don't leave stale entry in DB
                }
            }
        }
    }

    untiedb();
}


# Flag which hosts are up and recalculate who serves what if status has changed.
# Argument is a string of the form
# 0:DOWN|1:UP|2:UP|3:UP|4:UP|5:UP|6:UP|
sub check_desthosts($) {
    my ($str) = @_;
    my $statchanged;
    my %stats;

    foreach my $a (split /\|/, $str) {
        my ($i, $st) = split(/:/, $a, 2);
        next unless defined($i) && defined($st);

        if($st eq "UP") {
            if(!$hosts->[$i]->{up}) {
                notice "checkhost: $hosts->[$i]->{name} BAD -> OK\n";
                $hosts->[$i]->{up} = 1;

                # Only "real" redirect targets merit recalculation.
                if($hosts->[$i]->{weight}) {
                    $statchanged=1;
                }
            }
        }
        else {
            if($hosts->[$i]->{up}) {
                notice "checkhost: $hosts->[$i]->{name} OK -> BAD\n";
                delete $hosts->[$i]->{up};

                # Only "real" redirect targets merit recalculation.
                if($hosts->[$i]->{weight}) {
                    delete $hosts->[$i]->{left};
                    delete $hosts->[$i]->{right};
                    $statchanged=1;
                }
            }
        }

    }

    if($statchanged) {
        calc_intervals();
    }
}


# Given an fqdn, return the index to the matching host in the hosts array, 
# creating a new one if it doesn't exist.
sub get_desthost($$) {
    my $fqdn = shift;
    my $name = shift;
    my $i;

    for($i=0; $i <= $#$hosts; $i++) {
        if($hosts->[$i]->{fqdn} eq $fqdn) {
            return $i;
        }
    }

    # If host is not defined, create a bare-minimum entry for it.
    $i = scalar(@{$hosts});
    $hosts->[$i]->{name} = $name;
    $hosts->[$i]->{fqdn} = $fqdn;
    $hosts->[$i]->{up} = 1;
    if($name =~ /\./) {
        $hosts->[$i]->{checkuri} = $conf->{remotecheckuri};
    }

    return $i;
}


# Calculate a hash value that fits within $nbuckets.
sub calchash($) {
    my $str = shift;
    my $sum;
    my $ret;

    $ret = Math::BigInt->new("0x".md5_hex($str))->bmod($nbuckets);

    return($ret);
}

# Stat a file to get inode and size.
# Argument: URI
# Returns: List of inode and size if file exists.
sub get_inode_size($) {
    my $uri = shift;

    # stat uri, if it exists use inode as base for hashing. Note that 
    # we can't use dev since it's likely to be different on different hosts
    # which is bad when you want identical results regardless of which frontend
    # this runs on...
    my($inode, $size) = (stat("$conf->{docroot}/$uri"))[1,7];

    return($inode, $size);
}


# Stat a file to get mtime.
# Argument: filename
# Returns: mtime
sub get_mtime($) {
    my $file = shift;

    return (stat($file))[9];
}


# Find a hash value for this URI.
# Argument: URI and inode (if available).
# Returns: Hash value
sub findhash($$) {
    my $file = shift;
    my $ino = shift;
    my $str;
    my $hash;

    # Use inode if available, fallback to URI.
    if(defined($ino)) {
        $str = sprintf("%016lx", $ino);
    }
    else {
        $str = $file;
    }
    $hash = calchash($str);

#    debug "'$str' has hash: $hash\n";

    return $hash;
}


# Initiate state for fixed entries.
sub initfixed() {
    my $multihost = 0;
    my $k;

    while ($k = each %{$fixed}) {
        my ($inode, $size) = get_inode_size($k);
        my $hash = findhash($k, $inode);
        $fixed->{$k}{hash} = $hash;
        $fixedhvals{$hash} = $k;
        $fixed->{$k}{time} = time();
        for(my $i=0; $i <= $#{$fixed->{$k}{hosts}}; $i++) {
            my ($fqdn, undef) = getcanonnameandip($fixed->{$k}{hosts}->[$i]);
            if($fqdn) {
                push @{$fixed->{$k}{hostidx}}, get_desthost($fqdn, $fixed->{$k}{hosts}->[$i]);
            }
            else {
                warn "host $fixed->{$k}{hosts}->[$i] not found, ignoring\n";
            }
        }
        if(scalar @{$fixed->{$k}{hostidx}} > 1) {
            $multihost++;
        }
    }
    
    if($multihost > 0) {
        # No need to iterate between multiple hosts when there's only
        # one host there...
        notice "Multi-host fixed redirects found, enabling iterations.\n";
        $iterinterval = random_interval($conf->{iterintervalmin}, 
                                        $conf->{iterintervalmax});
    }

    # Ugly hack, but we need the check URI to always be resolved as local
    # as possible.
    # FIXME: This is only needed if the check URI something that is redirected
    # to us in the first place.
#    for(my $i=0; $i <= $#$hosts; $i++) {
#        push @{$fixed{$conf->{checkuri}}{hostidx}}, $i;
#    }
#    my $hash = findhash($conf->{checkuri});
#    $fixed{$conf->{checkuri}}{hash} = $hash;
#    $fixedhvals{$hash} = $conf->{checkuri};
#    $fixed{$conf->{checkuri}}{time} = time();
}


# Update locations for fixed objects.
sub updatefixed() {
    return unless(%fixedhvals);

    if(!tiedb()) {
        return;
    }

    my($key,$ref);
    while (($key,$ref) = each %entries) {
        my $newdest = findfixed($ref->{hash}, $ref->{size});
        next unless($newdest);
        if($newdest ne $ref->{val}) {
            debug "Change $key: $ref->{val} -> $newdest\n";
            $ref->{val} = $newdest;
            if($ref->{indb}) {
                eval {
                    $DB{$key} = $newdest;
                };
                if($@) {
                    error($@);
                    delete $DB{$key}; # Don't leave stale entry in DB
                }
            }
        }
    }

    untiedb();
}


# Update locations for files detected to cause a burst
sub updateburstfiles() {
    return unless(%burstfiles);

    if(!tiedb()) {
        return;
    }

    # As burst detection is based on the filename accessed it is enough to
    # only iterate through those files.
    my $key;
    while ($key = each %burstfiles) {
        next unless($entries{$key}); # Not likely, but...
        my $newdest = finddest(1, \$key, $entries{$key}{hash}, $entries{$key}{size});
        next unless($newdest);
        if($newdest ne $entries{$key}{val}) {
            debug "Change $key: $entries{$key}{val} -> $newdest\n";
            $entries{$key}{val} = $newdest;
            if($entries{$key}{indb}) {
                eval {
                    $DB{$key} = $newdest;
                };
                if($@) {
                    error($@);
                    delete $DB{$key}; # Don't leave stale entry in DB
                }
            }
        }
    }

    untiedb();
}


# Find a destination for a fixed redirect. Returns undef if not found.
sub findfixed($$) {
    my $hash = shift;
    my $size = shift;

    return undef unless ($fixedhvals{$hash});

    my $hostidx = $fixed->{$fixedhvals{$hash}}{hostidx};
    my @hostsup;
    for(my $i = 0; $i<=$#{$hostidx}; $i++) {
        if($myfqdn{$hosts->[$hostidx->[$i]]->{fqdn}}) {
            # If we're a member of the target, always say we want this entry
            # to avoid ping-pongs... Since we got the request through httpd
            # we know it's up at least ;)
            return "_";
        }
        if($hosts->[$hostidx->[$i]]->{up}) {
            push @hostsup, $hostidx->[$i];
        }
    }

    if($#hostsup < 0) {
        # If no targets are up fallback to dynamic redirects, even though
        # we might risk ping-pong for a while it's better than being
        # permanently broken.
        return undef;
    }

    $size = "-" unless($size);

    return "$hosts->[$hostsup[$iter % scalar(@hostsup)]]->{fqdn}_$size";
}


# Purge old records.
sub dopurge {
    my ($maxage, $cachelimit, $dblimit, $quick) = @_;
    my $key;

    my $now = time();
    my %fchanged;
    my $createnewdb = 0;

    if(!$quick) {
        # Re-stat all fixed redirects every time we're doing a purge.
        while ($key = each %{$fixed}) {
            my($inode, $size) = get_inode_size($key);
            my $newhash = findhash($key, $inode);
            if($newhash != $fixed->{$key}{hash}) {
                $fchanged{$fixed->{$key}{hash}} = $newhash;
                delete $fixedhvals{$fixed->{$key}{hash}};
                $fixedhvals{$newhash} = $key;
                $fixed->{$key}{hash} = $newhash;
                debug "Updated fixed redirect '$key'\n";
            }
            $fixed->{$key}{time} = $now;
        }

        my ($dbsize,$blksize) = (stat($dbfilename))[7,11];
        if(defined($blksize)) {
            my $dbmaxsize = $conf->{maxdb} * $blksize;
            if($dbsize > $dbmaxsize) {
                notice "DB size $dbsize larger than maxsize $dbmaxsize, reclaiming space by creating new DB file\n";
                
                $createnewdb = 1;
            }
        }
        else {
            warn "Couldn't stat $dbfilename: $!\n";
        }
            
    }

    if(!tiedb($createnewdb)) {
        return;
    }

    while ($key = each %entries) {
        # Revalidate dostatcheck entries by throwing them out and have
        # new accesses bring them in again. That spreads the time needed
        # to do the stat():s, doing them all at once can take tens of seconds
        # for tens of thousands of entries.
        if( $entries{$key}{dostatcheck} || 
            (($entries{$key}{btime} + $maxage < $now) && (!$quick || !$entries{$key}{indb} || $dblimit > 0)) )
        {
            # Delete old entry
            my $delorigin = "cache";
            if($entries{$key}{indb}) {
                delete $DB{$key};
                $dbentries--;
                $delorigin = "DB";
                $dblimit-- if($quick);
            }
            delete $entries{$key};
            $cachelimit-- if($quick);
            debug "Purged $key from $delorigin\n";
            if($quick) {
                last if($cachelimit<=0 && $dblimit<=0);
            }
            next;
        }

        if(defined $fchanged{$entries{$key}{hash}}) {
            # Handle updated fixed entries. This blindly assumes that
            # all our entries always points to the same file. This won't
            # always be true, but it avoids a lot of stat's and is good enough
            $entries{$key}{hash} = $fchanged{$entries{$key}{hash}};
        }
        if($createnewdb) {
            # Seed new DB file with all our entries
            eval {
                $DB{$key} = $entries{$key}{val};
            };
        }
    }

    untiedb();

    if(!$quick) {
        updatefixed();
        updateburstfiles();

        # Aim to do purging simultaneously on all hosts.
        $lastpurge = timestep($now, $conf->{purgeinterval});
    }
}


# The main loop of the child responsible for the actual polling of
# target hosts.
sub hostcheckloop() {
    $SIG{PIPE} = sub {exit;};

    my $ua = LWP::UserAgent->new (max_redirect => 0);

    $logprogname = 'redirprg-check';

    notice "Host status check child started\n";

    while(1) {
        my $stats = "";
        # Check which hosts are up.
        for(my $i=0; $i <= $#$hosts; $i++) {
            next unless $hosts->[$i]->{fqdn};

            # Handle manually disabled hosts
            my $disabled = $hosts->[$i]->{disabled};
            if($disabled && $disabled eq "yes") {
                $stats .= "$i:DISABLED|";
                next;
            }

            # Use longer timeout if the host was up before to not toggle
            # it just because of a backend load peak.
            if($hosts->[$i]->{up}) {
                $ua->timeout($conf->{longtimeout});
            }
            else {
                $ua->timeout($conf->{shorttimeout});
            }

            my $uri=$conf->{checkuri};
            if($hosts->[$i]->{checkuri}) {
                $uri = $hosts->[$i]->{checkuri};
            }
            # Use IP address here so we don't have to cater for DNS
            # issues affecting our timeout.
            my $resp = $ua->head("http://$hosts->[$i]->{hostip}$uri");
            if($resp->is_success) {
                if(!$hosts->[$i]->{up}) {
                    $hosts->[$i]->{up} = 1;
                }
                $stats .= "$i:UP|";
            }
            else {
                if($hosts->[$i]->{up}) {
                    delete $hosts->[$i]->{up};
                }
                $stats .= "$i:DOWN|";
            }
        }
        print "$stats\n" || exit;
        
        sleep $conf->{checkinterval};
    }
}


# Trigger caching of a file
sub triggercachefile ($)
{
    my $file = shift;
    my $origbf;

    # Temporarily add this file as a burst file to get the lookup right.
    if($burstfiles{$file}) {
        $origbf = $burstfiles{$file}{burstfactor};
        $burstfiles{$file}{burstfactor} ++;
    }
    else {
        $origbf = 0;
        $burstfiles{$file}{burstfactor} = 1;
    }

    # Do lookup, overriding iteration with a number matching the upcoming
    # offloader.
    my($inode, $size) = get_inode_size($file);
    my $hash = findhash($file, $inode);
    my $res = finddest(1, \$file, $hash, $size, $origbf+1);

    debug("triggercachefile: file: $file res: $res\n");

    # Restore burst file state
    if($origbf) {
        $burstfiles{$file}{burstfactor} = $origbf;
    }
    else {
        delete $burstfiles{$file};
    }

    my $host = (split /_/, $res)[0];

    my $url = "http://$host$file";

    my $ua = LWP::UserAgent->new(max_redirect => 0, timeout => $conf->{shorttimeout});

    my $resp = $ua->get($url, 'Range', 'bytes=0-511');

    if($resp->is_success) {
        debug("triggercachefile $url: SUCCESS\n");
        #debug("Headers: ".$resp->headers->as_string()."\n");
    }
    else {
        debug("triggercachefile $url: FAIL: ".$resp->status_line."\n");
    }
}


# Returns a parsed $conf->{offloadlogfile} name.
sub offloadlogfilename()
{
    return strftime($conf->{offloadlogfile}, localtime());
}

# The main loop of the child responsible for checking for files causing bursts.
sub burstcheckloop() {
    $SIG{PIPE} = sub {exit;};
    # Sleep when die():ing to avoid respawning too fast.
    $SIG{__DIE__} = sub {my $l = logpreamble('emerg').$_[0]; sleep 5; die($l);};

    $logprogname = 'redirprg-burst';

    notice "Burst check child started\n";

    my $timeout = 10;

    # Always reread the entire log file for today on startup. This only takes
    # a couple of seconds, and lets us (re)build statistics upon restart.
    my $log = File::Tail->new(name=>offloadlogfilename(), 
                                maxinterval=>int($timeout/2),
                                interval=>1, resetafter=>30, tail=>-1,
                                name_changes=>\&offloadlogfilename,
                                errmode=>'warn');

    my %seenfiles;
    my $lastpurge = time();

    # Push relevant config into the BurstDetector module.
    BurstDetector::set_config('default', 'debugprintfunc', sub {print STDERR logpreamble('debug'),@_;});
    my $maxmaxbw=0;
    for(my $i=0; $i <= $#$hosts; $i++) {
        my $maxbw = $hosts->[$i]->{maxbw};
        my $fqdn = $hosts->[$i]->{fqdn};
        next unless($maxbw && $fqdn);

        $maxbw *= 1000000; # MB/s -> bytes/s
        BurstDetector::set_config($fqdn, 'maxbw', $maxbw);
        if($maxbw > $maxmaxbw) {
            $maxmaxbw = $maxbw;
        }
    }
    if($maxmaxbw) {
        # Set fallback/default to be largest seen.
        BurstDetector::set_config('default', 'maxbw', $maxmaxbw);
    }

    BurstDetector::init();

    my $lastsave = BurstDetector::historyslot(time()-BurstDetector::get_config('default', 'historyslotsize')); # Force save on load
    my $histsavelag = $timeout + BurstDetector::get_config('default', 'timeslotlag');
    if(BurstDetector::history_load($conf->{historyfile})) {
        notice "Load $conf->{historyfile}: OK\n";
    }
    else {
        warn "Load $conf->{historyfile}: FAIL\n";
        my $dirname = (fileparse($conf->{historyfile}))[1];
        if(! -d $dirname) {
            make_path($dirname);
            warn "Created $dirname\n";
        }
    }

    # Base purge interval on the age of records
    my $spurgeinterval = $conf->{minseenexpire} * 2;

    while(1) {
        my ($nfound,$timeleft,@pending)=File::Tail::select(undef,undef,undef,$timeout,$log);

        if(scalar keys(%seenfiles) > $conf->{maxseenentries} 
                || $lastpurge + $spurgeinterval < time()) 
        {
            my $before = scalar keys(%seenfiles);
            my $cutoff = time();
            do {
                while (my ($key, $value) = each %seenfiles) {
                    if($value < $cutoff) {
                        delete $seenfiles{$key};
                    }
                }
                $cutoff += int($conf->{minseenexpire}/24)+1;
            } while(scalar keys(%seenfiles) > $conf->{maxseenentries});
            my $after = scalar keys(%seenfiles);
            $lastpurge = time();
            if($before != $after) {
                debug("Purged old ip:file records, before=$before after=$after\n");
            }
        }

        my @res;
        my $time;
        if($nfound) {
            my $line = $log->read;
            # 1580570309.494 127.22.123.45 GET host.ftp.acc.umu.se 10969556 /ubuntu/pool/main/l/linux-hwe/linux-headers-5.3.0-28_5.3.0-28.30~18.04.1_all.deb
            if($line =~ /^(\d+)\S*\s(\S+)\sGET\s(\S+)\s(\d+)\s(.+)$/) {
                $time = $1;
                my $ip = $2;
                my $target = $3;
                my $size = $4;
                my $file = $5;

                # Avoid registering parallel downloaders as multiple downloads
                if($seenfiles{"$ip:$file"} && $seenfiles{"$ip:$file"} >= int($time)) {
                    next;
                }

                # Base the ip:file expire time on the size, bigger files
                # take longer to download and thus have higher probability of
                # seeing parallel downloads.
                my $expire = int($size/$conf->{seenexpiresizefactor});
                if($expire < $conf->{minseenexpire}) {
                    $expire = $conf->{minseenexpire};
                }
                $seenfiles{"$ip:$file"} = int($time) + $expire;

                @res = BurstDetector::reg_offload($time, $target, $size, $file);
            }
            else {
                # Just skip unparse:able lines
                next;
            }
        }
        else {
            # For housekeeping, lag time to be more in sync with lagged logs
            $time = time() - $timeout;
            @res = BurstDetector::reg_offload($time, undef, undef, undef);
        }
        while(my($file, $bf) = splice(@res, 0, 2)) {
            print "$bf=$file\n";
        }
        if($lastsave < BurstDetector::historyslot($time-$histsavelag)) {
            if(BurstDetector::history_save($conf->{historyfile})) {
                notice "Save $conf->{historyfile}: OK\n";
                $lastsave = BurstDetector::historyslot($time);
            }
            else {
                warn "Save $conf->{historyfile}: FAIL\n";
            }
        }
    }
}


# Spawn a child to take care of the status of the targets.
sub inithostcheck() {
    my $pid;
    my $sleep_count = 0;

    do {
        $pid = open(HOSTCHECK, "-|");
        unless (defined $pid) {
            warn "cannot fork: $!";
            die "bailing out" if $sleep_count++ > 10;
            sleep 2;
        }
    } until defined $pid;

    if(!$pid) { # child
        $| = 1; # Disable buffering...
        hostcheckloop();
        exit;
    }

    return $pid;
}


# Spawn a child to handle checking for bursts
sub initburstcheck() {
    my $pid;
    my $sleep_count = 0;

    do {
        $pid = open(BURSTCHECK, "-|");
        unless (defined $pid) {
            warn "cannot fork: $!";
            die "bailing out" if $sleep_count++ > 10;
            sleep 2;
        }
    } until defined $pid;

    if(!$pid) { # child
        $| = 1; # Disable buffering...
        burstcheckloop();
        exit;
    }

    return $pid;
}

# Get number of seconds left to timeout
sub timeleft
{
    my($last, $timeout) = @_;

    my $left = $last + $timeout - time();
    if($left < 0) {
        $left = 0;
    }

    return $left;
}


# ============================================================================
# main()

getopts('tq', \%opts) || die "Usage error";

# Default to finding config in same dir as this script, but allow
# passing the cfgbase as argument.
my $cfgbase         = dirname(__FILE__) . "/redirprg";
if($ARGV[0]) {
    $cfgbase = $ARGV[0];
}
my $cfgmain         = "$cfgbase.conf";
my $cfghosts        = "$cfgbase-hosts.conf";
my $cfgfixed        = "$cfgbase-fixed.conf";

if(! $opts{t}) {
    $SIG{__DIE__} = sub {my $l = logpreamble('emerg').$_[0]; die($l);};
    $SIG{__WARN__} = sub{print STDERR logpreamble('warn'),$_[0];};
};

# Disable buffering
$| = 1;

$conf = readmainconf($cfgmain);
die "$cfgmain broken" unless($conf);

if($conf->{maxcache} < $conf->{maxdb}) {
    error("config: maxcache must be at least as large as maxdb, overriding\n");
    $conf->{maxcache} = $conf->{maxdb};
}

if($opts{q}) {
    $conf->{loglevel} = 'error';
}

my $lastcfgcheck = timestep(time(), $conf->{cfgcheckinterval});

my $hostsmtime = get_mtime($cfghosts);
$hosts = readhostsconf($cfghosts);
die "$cfghosts broken" unless($hosts);

my $fixedmtime = get_mtime($cfgfixed);
$fixed = readfixedconf($cfgfixed);
die "$cfgfixed broken" unless($fixed);

if($opts{t}) {
    notice "Config files tested OK:\n\t$cfgmain\n\t$cfghosts\n\t$cfgfixed\n";
    notice "Exiting...\n";
    exit 0;
}

debug("Loaded configuration from $cfgmain\n");
debug("Loaded configuration from $cfghosts\n");
debug("Loaded configuration from $cfgfixed\n");

# Init last purge timestamp.
$lastpurge = timestep(time(), $conf->{purgeinterval});

# Init new empty DB
if(tiedb(1)) {
    untiedb();
}

get_myfqdn();
resolve_desthosts();
initfixed();
calc_intervals();
my $hostcheckpid = inithostcheck();
my $burstcheckpid;
if(!$is_desthost) {
    # Burst file detection only makes sense on Frontends...
    $burstcheckpid = initburstcheck();
}

sub catch_sig {
    my $signame = shift;
    notice "Killed by $signame. Exiting...\n";
    kill("TERM", $hostcheckpid);
    if($burstcheckpid) {
        kill("TERM", $burstcheckpid);
    }
    exit;
}

# die() handler, but not in eval{}...
$SIG{__DIE__} = sub {die @_ if $^S; my $l = logpreamble('emerg').$_[0]; print STDERR $l; catch_sig("DIE");};

$SIG{'INT'}=$SIG{'HUP'}=$SIG{'TERM'} = \&catch_sig;

my $sel = IO::Select->new(\*STDIN, \*HOSTCHECK);
if($burstcheckpid) {
    $sel->add(\*BURSTCHECK);
}

notice "redirprg.pl started\n";

# Sit in this loop forever, serving targets for URI:s one at a time.
while(1) {
    my $to = timeleft($lastcfgcheck, $conf->{cfgcheckinterval});
    my $pto = timeleft($lastpurge, $conf->{purgeinterval});
    if($pto < $to) {
        $to = $pto;
    }

    my $ito;
    if($iterinterval) {
        $ito = timeleft($lastiter, $iterinterval);
        if($ito < $to) {
            $to = $ito;
        }
    }
    my @ready = $sel->can_read($to);
    if(! @ready) {
        # No fd's, maintenance time.
        if(defined($ito) && timeleft($lastiter, $iterinterval) <= 0) {
            $iter++;
            if($iter < 0) {
                $iter = 0;
            }
            debug "Updating multi-target redirects, iteration $iter\n";
            updatefixed();
            updateburstfiles();
            $iterinterval = random_interval($conf->{iterintervalmin}, 
                                            $conf->{iterintervalmax});
            $lastiter = time();
        }
        elsif(timeleft($lastpurge, $conf->{purgeinterval}) <= 0) {
            notice "DB Purge start, periodic, before: cache=".scalar keys(%entries)." db=$dbentries\n";
            dopurge($conf->{maxage});
            notice "DB Purge done, periodic, after: cache=".scalar keys(%entries)." db=$dbentries\n";
        }
        else {
            my $newhmtime = get_mtime($cfghosts);
            if($newhmtime > $hostsmtime) {
                my $newhostsmtime = get_mtime($cfghosts);
                my $newhosts = readhostsconf($cfghosts);
                if($newhosts) {
                    $hosts = $newhosts;
                    $hostsmtime = $newhostsmtime;
                    resolve_desthosts();
                    calc_intervals();

                    # Kill off children, forcing them to restart with fresh
                    # config.
                    kill("TERM", $hostcheckpid);
                    if($burstcheckpid) {
                        kill("TERM", $burstcheckpid);
                    }
                    notice "$cfghosts reloaded.\n";
                }
                else {
                    error "$cfghosts broken, ignored.\n";
                }
            }
            my $newfmtime = get_mtime($cfgfixed);
            if($newfmtime > $fixedmtime) {
                my $newfixedmtime = get_mtime($cfgfixed);
                my $newfixed = readfixedconf($cfgfixed);
                if($newfixed) {
                    $fixed = $newfixed;
                    $fixedmtime = $newfixedmtime;
                    %fixedhvals = ();
                    initfixed();
                    calc_intervals();
                    notice "$cfgfixed reloaded.\n";
                }
                else {
                    error "$cfgfixed broken, ignored.\n";
                }
            }

            # Synchronize config reload across hosts.
            $lastcfgcheck = timestep(time(), $conf->{cfgcheckinterval});
        }
        next;
    }
    foreach my $f (@ready) {
        if($f->eof) {
            # Handle EOF's of various kinds.
            if($f == \*STDIN) {
                notice "STDIN: EOF. Exiting...\n";
                kill("TERM", $hostcheckpid);
                if($burstcheckpid) {
                    kill("TERM", $burstcheckpid);
                }
                exit 0;
            }
            elsif($f == \*HOSTCHECK) {
                warn "Host-check child died. Restarting.\n";
                $sel->remove($f);
                $hostcheckpid = inithostcheck();
                $sel->add(\*HOSTCHECK);
            }
            elsif($burstcheckpid && $f == \*BURSTCHECK) {
                warn "Burst-check child died. Restarting.\n";
                $sel->remove($f);
                $burstcheckpid = initburstcheck();
                $sel->add(\*BURSTCHECK);
            }
            else {
                warn "ERROR: EOF from unknown source. Ignoring.\n";
            }
            next;
        }
        my $str = $f->getline;
        chomp $str;

        if($f == \*STDIN) {
            my $res;
            my $state;

            # If entry is cached, return it.
            if(exists($entries{$str})) {
                $res = $entries{$str}{val};
                $state = "cached";

                $entries{$str}{hits}++;

                # Evaluate whether entry has enough hits to warrant
                # promotion to DB.
                if(!$entries{$str}{indb}) {
                    # Require last hit to be recent
                    if($entries{$str}{atime} + $conf->{maxhitage} < time()) {
                        $entries{$str}{hits} = 1;
                    }

                    $entries{$str}{atime} = time();

                    # Yup, it's popular!
                    if($entries{$str}{hits} >= $conf->{hitspromote}) {
                        if(tiedb()) {
                            eval {
                                $DB{$str} = $res;
                            };
                            if($@) {
                                error($@);
                            }
                            untiedb();
                            # We'll never need these again
                            delete $entries{$str}{hits};
                            delete $entries{$str}{atime};

                            $entries{$str}{indb} = 1;
                            $dbentries++;
                            $state .= " (promoted to DB)";
                        }
                    }
                }

            }
            else {
                my($inode, $size) = get_inode_size($str);
                my $hash = findhash($str, $inode);
                $res = findfixed($hash, $size);
                if(!$res) {
                    $res = finddest(0, \$str, $hash, $size);
                }
                $state = "new";
                my $info = "hash: $hash";

                $entries{$str}{btime} = $entries{$str}{atime} = time();
                $entries{$str}{size}  = $size;
                $entries{$str}{hash}  = $hash;
                $entries{$str}{val}   = $res;
                $entries{$str}{hits}  = 1;

                if($str =~ /$conf->{changinguris}/i) {
                    $entries{$str}{dostatcheck} = 1;
                    $info .= ", dostatcheck";
                }
                if(defined($inode)) {
                    $info .= sprintf(", inode: 0x%lx", $inode);
                }
                if(defined($size)) {
                    $info .= ", size: $size";
                }
                $state .= " ($info)";
            }

            print "$res\n";
            debug "$state: '$str' -> $res\n";
        }
        elsif($f == \*HOSTCHECK) {
            debug "hoststatus: $str\n";
            check_desthosts($str);
        }
        elsif($burstcheckpid && $f == \*BURSTCHECK) {
            if($str =~ /^(\w+)=(.*)$/) {
                my $burstfactor = $1;
                my $file = $2;
                if($burstfactor && $burstfactor =~ /[A-Z]/) {
                    triggercachefile($file);
                }
                elsif($burstfactor) {
                    $burstfiles{$file}{burstfactor} = $burstfactor;
                    push @{$burstfiles{$file}{times}}, time();
                    notice "File burst, factor $burstfactor: $file\n";
                }
                else {
                    delete $burstfiles{$file};
                    notice "File burst, revert to normal: $file\n";
                }
                if((%burstfiles || %fixedhvals) ) {
                    if(!$iterinterval) {
                        $iterinterval = random_interval($conf->{iterintervalmin}, $conf->{iterintervalmax});
                        notice "Bursty file(s) found, enabling iterations.\n";
                    }
                }
                else {
                    $iterinterval = undef;
                    notice "No longer any bursty files, disabling iterations.\n";
                }
            }
            else {
                warn "ERROR: burstcheck: Unknown message: '$str'\n";
            }
        }
        else {
            warn "ERROR: Ignoring data from unknown filehandle: '$str'\n";
        }
    }

    # Purge cache and DB if we get too many entries.
    if(scalar keys(%entries) > $conf->{maxcache} || $dbentries > $conf->{maxdb}) {
        notice "DB Purge start, overflow, before: cache=".scalar keys(%entries)." db=$dbentries\n";
        my $cachelimit = int($conf->{maxcache} * 0.01);
        my $cachethreshold = $conf->{maxcache} - $cachelimit;
        my $dblimit = int($conf->{maxdb} * 0.01);
        my $dbthreshold = $conf->{maxdb} - $dblimit;
        my $age = int($conf->{maxage} / 2);
        for(; scalar keys(%entries) > $cachethreshold || $dbentries > $dbthreshold; $age = int($age / 2)) {
            $cachelimit = scalar keys(%entries) - $cachethreshold;
            $dblimit = $dbentries - $dbthreshold;
            dopurge($age, $cachelimit, $dblimit, 1);
        }
        notice "DB Purge done, overflow, after: cache=".scalar keys(%entries)." db=$dbentries using maxage=$age\n";
    }
}
