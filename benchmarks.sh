#!/bin/bash

function help {
  cat <<EOF
benchmarks.sh - a tool to manage our suite of Puppet benchmarks

benchmarks.sh upload:

Upload locally modified benchmarks to the Google Storage bucket.

benchmarks.sh download:

Download benchmarks from the Google Storage bucket.

Neither command will delete files. Run gsutil manually with the -d flag
if needed.
EOF
}

if [ $# -ne 1 ]; then
  help
  exit 1
fi

mkdir -p benchmarks

case "$1" in
  upload)
    gsutil -m rsync -r benchmarks gs://puppet-benchmarks
    ;;
  download)
    gsutil -m rsync -r gs://puppet-benchmarks benchmarks
    ;;
  *)
    echo "Invalid arguments"
    help
    exit 1
esac





