#!/bin/bash

#java -cp $LIB_SDG/jars-external/java-cup-11a.jar java_cup.Main \
java -cp ../../../../../../../../../cnf/jars/java-cup-11a.jar:../../../../../../../../../cnf/jars/java-cup-runtime-0.11-a-czt01-cdh.jar java_cup.Main \
 -package edu.mit.csail.sdg.parser \
 -parser CompParser \
 -progress -time -compact_red \
 -symbols CompSym < Alloy.cup
