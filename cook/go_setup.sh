#! /bin/bash

cat golang.seed | debconf-set-selections
apt-get install -q -y golang
