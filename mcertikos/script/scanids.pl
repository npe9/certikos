#!/usr/bin/perl -w

my %ids;
while (<>) {
	foreach (/(\w+) *↦/) {
		$ids{$1} = 1 if length($1) > 2;
	}
}

foreach (sort keys(%ids)) {
	print "($_, \"$_\") ::\n";
}

