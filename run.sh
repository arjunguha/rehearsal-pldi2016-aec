#!/bin/bash
ARGS=$@
sbt  --warn "set showSuccess in ThisBuild := false" "project rehearsal" "run $ARGS"
