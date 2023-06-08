#!/bin/bash

WORKSPACE=/Users/admin/project/tlc/tlaplus/git/tlaplus/tlatools/org.lamport.tlatools
TESTDIR=$WORKSPACE/test-CC

TLATools=$TESTDIR/scripts/jar/tla2tools.jar
MAINCLASS=tla2sany.SANY
SPECNAME=raft
DOTNAME=dump
SPECDIR=$TESTDIR/$SPECNAME
SPECTLA=$SPECDIR/$SPECNAME.tla
SPECCFG=$SPECDIR/$SPECNAME.cfg
DOTFILE=$SPECDIR/$DOTNAME.dot
SVGFILE=$SPECDIR/$DOTNAME.svg

ARGS_SPEC="-d ${SPECTLA}"
ARGS_OTHERS="-tool -modelcheck"
ARGS_DOT="-dump dotactionlabels ${DOTFILE}"

ANTFILE=$WORKSPACE/customBuild.xml
ANTTARGET=dist

cd $SPECDIR
java -cp $TLATools $MAINCLASS  $ARGS_SPEC