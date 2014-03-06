#! /bin/bash

apt-get install couchdb

cat <<__EOF__ > /etc/couchdb/local.ini
[httpd]
bind_address = \"$HOST\"
port = \"$PORT\"
__EOF__

service couchdb restart
