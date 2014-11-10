#!/bin/bash
set -x
set -e

cd `dirname $0`

mkdir -p z3/4.3-unix-64b

pushd z3
autoconf
./configure --prefix=/home/vagrant/src/ScalaZ3/z3/4.3-unix-64b
python scripts/mk_make.py
cd build
make
sudo make install
popd

pushd ScalaZ3
sbt publishLocal
popd
