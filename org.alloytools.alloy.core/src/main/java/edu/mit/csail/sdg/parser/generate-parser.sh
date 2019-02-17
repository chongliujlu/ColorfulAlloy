#!/bin/bash

java -jar ../../../../../cup-11a.jar \
 -package edu.mit.csail.sdg.parser \
 -parser CompParser \
 -progress -time -compact_red \
 -symbols CompSym < Alloy.cup 
