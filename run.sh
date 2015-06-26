#!/bin/bash
ARGS=$@
sbt -Dorg.slf4j.simpleLogger.defaultLogLevel=info  --warn "set showSuccess in ThisBuild := false" "project rehearsal" "run $ARGS"
