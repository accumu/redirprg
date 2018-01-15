# Introduction

An Apache HTTPD RewriteMap program for choosing an offload target suitable
for requested URI.

Developed to meet the needs of http://ftp.acc.umu.se/ - the file archive of
Academic Computer Club (ACC), Umeå University, Sweden. The archive hosts
all kinds of Open Source software ranging from small archive files to
large DVD images.

ftp.acc.umu.se consists of a backend server delivering a shared file system
via NFS to multiple frontend servers running this RewriteMap program to
redirect suitable traffic to dedicated offloader servers.  This RewriteMap
program is aware of the methods used by `mod_cache_disk_largefile`, available
at https://github.com/accumu/mod_cache_disk_largefile, to avoid duplicated
files in the cache and tries to ensure that only one primary offloader is
chosen to handle each file and all its duplicate names.

Among the features are on-the-fly reconfiguration of available redirection
targets, burst detection of single-file hotspots and caching of results in a
GDBM map to speed up subsequent requests.

This work eventually became a part of the Master's thesis *Scaling a Content
Delivery system for Open Source Software*, available at
http://urn.kb.se/resolve?urn=urn:nbn:se:umu:diva-109779

# Installation

Requires perl and a few common modules, see the script for details.

# Setup/config

## Redirprg

The example `redirprg*.conf` files should be used as a base for your
configuration. The format is JSON with comments.

Do note that the config handling is very rudimentary,
and not at all forgiving when it comes to parse errors or missing config
items. Patches welcome :-)

Using the included `test-json.pl` script is recommended to verify syntax
before applying to production hosts.

The script is started by Apache HTTPD, and thus needs to be present
in the Apache HTTPD configuration.

## Apache HTTPD

FIXME:
* Document quirks like logs needed and log formats
* Add httpd.conf config snippet
