#!/usr/bin/perl
# vim:et:ts=4:sw=4:ai:

# Copyright 2007 Niklas Edmundsson <nikke@acc.umu.se>
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

use GDBM_File;
use Fcntl;

my %DB;
my $dbfile = "/var/run/apache2.redirdb";

tie (%DB, 'GDBM_File', $dbfile, O_RDONLY, 0644) or die "Couldn't open $dbfile!\n";

my $summary=0;
if($ARGV[0] && $ARGV[0] eq "-c") {
    $summary = 1;
}


my %stats;
my $key;
my $val;
while (($key,$val) = each %DB) {
    if(! $summary) {
        print "$key -> $val\n";
    }
    if(!$stats{$val}) {
        $stats{$val} = 1;
    }
    else {
        $stats{$val}++;
    }
}

if($summary) {
    foreach my $k (sort keys %stats) {
        my $n = $k;
        if($n eq "_") {
            $n = "No Redirect";
        }
        printf "%-24s %4d\n", $n, $stats{$k};
    }
}
