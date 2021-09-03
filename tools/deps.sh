#!/bin/sh
echo "digraph oqarina_deps { "
echo "size=\"26,14\"; ratio = fill;"
echo "node [shape=ellipse,  style=filled, color=black];"

coqdep -f _CoqProject |
	sed -n -e 's,/,.,g;s/[.]vo.*: [^ ]*[.]v//p' |
	while read src dst; do
	    color=$(echo "$src" | sed -e 's,src.*,turquoise,;s,extraction.*,plum,')
	    echo "\"$src\" [fillcolor=$color];"
	    for d in $dst; do
	      echo "\"$src\" -> \"${d%.vo}\" ;"
	    done
	  done;
	echo "}"
