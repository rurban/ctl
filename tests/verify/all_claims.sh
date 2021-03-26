#!/bin/sh
# main.2-5 not yet supported
satabs --show-claims -I. $@ 2>/dev/null | \
    perl -lne'/Claim (\w+.\d+):/ && print "$1"' | \
    grep -v 'main.[2345]'
