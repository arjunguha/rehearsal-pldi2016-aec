class os {

  file { '/tmp':
    ensure => directory,
    mode   => '1777',
    owner  => root,
    group  => root
  }

  case $::operatingsystem {
    debian: {
      case $::lsbdistcodename {
        wheezy: {
          include os::debian-wheezy
        }
        squeeze: {
          include os::debian-squeeze
        }
        lenny: {
          include os::debian-lenny
        }

        default: {
          fail "Unsupported Debian version '${::lsbdistcodename}' in 'os' module"
        }
      }
    }

    CentOS,RedHat: {
      include os::centos
    }
    default: {
      fail "Unsupported OS ${::operatingsystem} in 'os' module"
    }
  }
}
