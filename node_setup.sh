#! /bin/bash

VERSION="v0.10.26"
PLATFORM="linux"
ARCH="x64"

cd /tmp && wget http://nodejs.org/dist/$VERSION/node-$VERSION-$PLATFORM-$ARCH.tar.gz
cd /usr/local && tar --strip-components 1 -xzf /tmp/node-$VERSION-$PLATFORM-$ARCH.tar.gz
