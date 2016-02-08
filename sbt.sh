#!/bin/bash
ARGS=$@

if [[ `uname` -eq "Darwin" ]]; then
  echo "Logging to ~/Library/Logs/rehearsal.log"
  LOGFILE=~/Library/Logs/rehearsal.log
else
  LOGFILE=rehearsal.log
fi

sbt -J-Xmx4G -Dorg.slf4j.simpleLogger.defaultLogLevel=info \
  -Dorg.slf4j.simpleLogger.logFile=$LOGFILE
