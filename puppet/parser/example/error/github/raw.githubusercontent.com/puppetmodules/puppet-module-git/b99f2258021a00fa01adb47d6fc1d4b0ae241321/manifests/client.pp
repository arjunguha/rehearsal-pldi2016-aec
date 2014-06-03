# Class: git
#
# This class installs git client
#
# Sample Usage:
#  include git::client
#

class git::client {
  case $operatingsystem {
    centos, redhat, debian, ubuntu: { $package_name = 'git' }
    default: { $package_name = 'git-core' }
  }

  package { $package_name:
    ensure => installed,
  }
}

  }
}
