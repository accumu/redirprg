#!/usr/bin/perl

# Copyright 2016 Niklas Edmundsson <nikke@acc.umu.se>
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

#
# Parses JSON file with comments, typically config files.
#

use warnings;
use strict;

use JSON;
use Data::Dumper;

my $ref;

# Read file and remove comments.
my @cfg = grep(!/^\s*#/, (<>));

# join everything into one line and decode.
# decode_json croaks on error, resulting in program exit on error.
$ref = decode_json(join "", @cfg);

print Dumper $ref;

exit 0;
