#!/bin/bash

WORKSPACE=/Users/admin/project/tlc/tlaplus/git/tlaplus/tlatools/org.lamport.tlatools
TLATools=$WORKSPACE/dist/tla2tools.jar
MAINCLASS=tlc2.TLC

SPECDIR=$WORKSPACE/test-CC/Paxos
SPECTLA=$SPECDIR/Paxos.tla
SPECCFG=$SPECDIR/Paxos.cfg
DOTFILE=$SPECDIR/dump.dot
SVGFILE=$SPECDIR/dump.svg

ARGS_SPEC="${SPECTLA} -config ${SPECCFG}"
ARGS_OTHERS="-tool -modelcheck"
ARGS_DOT="-dump dotactionlabels ${DOTFILE}"

ANTFILE=$WORKSPACE/customBuild.xml
ANTTARGET=dist


cd $WORKSPACE
ant -f $ANTFILE $ANTTARGET

cd $SPECDIR
java -cp $TLATools $MAINCLASS  $ARGS_SPEC $ARGS_OTHERS $ARGS_DOT
dot -Tsvg -o $SVGFILE $DOTFILE