#!/usr/bin/perl -w
require strict;

# Slurp the whole file
local $/;
local $_ = <>;

# <Your $_-modifying rules here>
s/asmsem (.*?)_spec_low_step/asmsem $1 $1_spec_low_step/sg;

print;
