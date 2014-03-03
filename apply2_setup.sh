#! /bin/bash

git clone https://github.com/plasma-umass/Apply2.git
cd Apply2
make


# Create and run a sample department
./apply2 newdept sample
./apply2 newreviewer scooby redbull64 "Scooby Doo"
