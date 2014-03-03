#! /bin/bash

wget http://nodejs.org/dist/v0.10.25/node-v0.10.25.tar.gz && tar -xzf node-v0.10.25.tar.gz && cd node-v0.10.25 && ./configure && make -j$(($(nproc) + 1)) && make install

