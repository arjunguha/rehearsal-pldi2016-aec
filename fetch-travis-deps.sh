#!/bin/bash
if [ -d "/home/travis/mydeps" ]; then
  echo "/home/travis/mydeps exists, so not fetching any dependencies"
  exit 0
fi

cd /home/travis
mkdir deps
cd deps

ZIPFILE=z3-4.4.1-x64-ubuntu-14.04.zip
URL=https://github.com/Z3Prover/z3/releases/download/z3-4.4.1/$ZIPFILE
wget $URL
unzip $ZIPFILE
mv z3-4.4.1-x64-ubuntu-14.04 z3

git clone https://github.com/regb/scala-smtlib.git
cd scala-smtlib
git checkout 711e9a1ef994935482bc83ff3795a94f637f0a04
sbt publish-local

