#!/bin/sh -e
find -name \*.v | while read f; do
	./script.pl $f > $f.n
	if cmp -s $f $f.n; then
		rm $f.n
	else
		mv $f.n $f
	fi
done
