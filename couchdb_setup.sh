#! /bin/bash

curl -X PUT http://127.0.0.1:5984/_config/httpd/bind_address -d \"0.0.0.0\"
curl -X PUT http://127.0.0.1:5984/_config/httpd/port -d \"$port\"

# curl -X PUT http://127.0.0.1:5984/_config/httpd/port -d \"$port\"

# cat <<__EOF__ > /etc/couchdb/local.ini
# [httpd]
# bind_address = 0.0.0.0
# port = $port
# __EOF__

# service couchdb restart
#curl -X put http://127.0.0.1:5984/_config/httpd/bind_address -d "$host"
#curl -X put http://127.0.0.1:5984/_config/httpd/port -d "$port"

# cat <<__EOF__ > /tmp/restart_couchdb.py
# import os
# os.system ("service couchdb restart")
# __EOF__
# python /tmp/restart_couchdb.py &

# exit $?
