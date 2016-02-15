#!/bin/bash
ARGS=$@

LOGFILE=rehearsal.log

sbt -J-Xmx4G -Dorg.slf4j.simpleLogger.defaultLogLevel=info \
  -Dorg.slf4j.simpleLogger.logFile=$LOGFILE
