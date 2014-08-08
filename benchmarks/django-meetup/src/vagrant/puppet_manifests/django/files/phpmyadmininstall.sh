#!/bin/bash

srcfile="/tmp/vagrant-puppet/manifests/files/phpmyadmin/phpMyAdmin.tar.gz"
installdir="/var/www/phpmyadmin/"

tar -xzf $srcfile -C $installdir/
chown root.www-data -R $installdir
find $installdir -type d -print0|xargs -0 chmod 755
find $installdir -type f -print0|xargs -0 chmod 644

echo "Setting up database for phpmyadmin..."
mysql -uroot -ppassword -e "create database phpmyadmin"
mysql -uroot -ppassword phpmyadmin < /tmp/vagrant-puppet/manifests/files/phpmyadmin/create_tables.sql