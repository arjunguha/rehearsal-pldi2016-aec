
# Default Paths
Exec { path => [ "/bin/", "/sbin/" , "/usr/bin/", "/usr/sbin/", "/usr/local/bin/", "/usr/local/sbin" ] }

# Includes
include params
include bootstrap
include apache
include php
include mysql
include backup
include phpmyadmin
include ssh
include project
