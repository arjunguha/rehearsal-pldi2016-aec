#!/bin/bash
copath="/usr/local/src/django"
djangorepo="https://github.com/django/django.git"

# Removing old repo clone if exits
rm -rf /usr/local/src/django/
mkdir -p /usr/local/src/django/
cd /usr/local/src/django/
git clone $djangorepo $copath/

cd /usr/local/src/django
git checkout stable/1.5.x
python setup.py install

# restart apache to reload the django processes under new version
service apache2 restart
