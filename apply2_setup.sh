#! /bin/bash

cd /tmp && git clone https://github.com/nimishgupta/Apply2.git && cd Apply2 && make

# Create and run a sample department
/tmp/Apply2/apply2 newdept sample
/tmp/Apply2/apply2 newreviewer scooby redbull64 "Scooby Doo"
/tmp/Apply2/apply2 -dbhost $host -dbport $port
