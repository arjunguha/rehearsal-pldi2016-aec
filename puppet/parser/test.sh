#! /bin/bash

find . -iname "*.pp" -exec echo '"run {}" ' \; | xargs sbt | tee out.txt
