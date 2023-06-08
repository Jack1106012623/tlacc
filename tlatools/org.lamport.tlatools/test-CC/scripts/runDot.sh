#! /bin/bash

WORKSPACE=/Users/admin/project/tlc/tlaplus/git/tlaplus/tlatools/org.lamport.tlatools
SPECNAME=Raft
SPECDIR=$WORKSPACE/test-CC/$SPECNAME
DOTFILE=$SPECDIR/dump.dot
SVGFILE=$SPECDIR/dump.svg



cd $SPECDIR
dot -Tsvg -o $SVGFILE $DOTFILE