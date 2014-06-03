# == Class: liferay
#
# Due to use sun proprietary code liferay on openjdk is not recommended, proteon/java module provides a way to include sun java in
# the process.
#
# === Parameters
#
# === Variables
#
# === Examples
#
# === Authors
#
# Sander Bilo <sander@proteon.nl>
#
# === Copyright
#
# Copyright 2013 Proteon.
#
class liferay {
    include java
}