# Class: etckeeper
#
# This class installs and configures etkceeper with git
#
# Parameters:
#   $highlevel_package_manager:
#       this variable sets the high level package manager depending on your OS
#   $lowlevel_package_manager:
#       this variable sets the low level package manager depending on your OS
#
# Actions:
#   Install etckeeper, create config and initialize git repository in /etc
#
# Requires:
#   - Package['git'] or ['git-core'] depending on your OS
#
# Sample Usage:
#   include etckeeper
#
class etckeeper {
  case $operatingsystem {
    /(RedHat|Fedora|CentOS|Scientific)/: {
      $highlevel_package_manager = "yum"
      $lowlevel_package_manager ="rpm"
    }
    /(Debian|Ubuntu)/: {
      $highlevel_package_manager = "apt"
      $lowlevel_package_manager ="dpkg"
    }
    default: { fail("Don't know how to handle ${operatingsystem}") }
  }

  package { etckeeper: ensure => installed; }

  file {
    "/etc/etckeeper/etckeeper.conf":
      ensure => present,
      content => template("etckeeper/etckeeper.conf.erb"),
      require => Package["etckeeper"];
  }

  Exec { path => ["/usr/bin", "/usr/sbin"] }

  exec {
    "etckeeper_init":
      command => "etckeeper init",
      creates => "/etc/.git",
      require => File["/etc/etckeeper/etckeeper.conf"];
  }
}
