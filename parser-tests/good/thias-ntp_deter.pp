include ntp

# Main class, see README for examples.

# NOTE(arjun): removed inherits
class ntp (
  $package_name = "ntp",
  $service_name = "ntpd",
  $config_file  = '/etc/ntp.conf',
  $template     = "ntp/ntp.conf-rhel.erb", # NOTE(arjun): removed $module_name
  $tinker       = [],
  $server       = [
    '0.rhel.pool.ntp.org',
    '1.rhel.pool.ntp.org',
    '2.rhel.pool.ntp.org',
  ],
  $restrict     = [
    'default kod nomodify notrap nopeer noquery',
    '-6 default kod nomodify notrap nopeer noquery',
  ],
  $logfile      = false,
) { # inherits ::ntp::params {

  # Main package and service it provides
  package { $package_name: ensure => 'installed' }
  service { $service_name:
    ensure    => 'running',
    enable    => true,
    hasstatus => true,
    require   => Package[$package_name],
  }

  # When using chronyd, stop and disable the old ntpd 'just in case'
  # (apparently, some public cloud instances of CentOS 7 default to ntpd)
  if $service_name == 'chronyd' {
    service{'ntpd':
      ensure => 'stopped',
      enable => false,
      before => Service['chronyd'],
    }
  }

  # Main configuration file
  file { $config_file:
    owner   => 'root',
    group   => 'root',
    mode    => '0644',
    content => template($template),
    before => Package[$package_name],
    notify  => Service[$service_name],
  }

  if $logfile != false and $service_name == 'ntpd' {
    # Logrotate for our custom log file
    file { '/etc/logrotate.d/ntpd':
      owner   => 'root',
      group   => 'root',
      mode    => '0644',
      content => template("${module_name}/ntpd-logrotate.erb"),
    }
  }

}
# Trivial parameters class inherited from the main class.
#
class ntp::params {

  case "${::osfamily}-${::operatingsystemmajrelease}" {
    /^Gentoo/: {
      $package_name = 'net-misc/ntp'
      $service_name = 'ntpd'
      $config_file = '/etc/ntp.conf'
      $template = "${module_name}/ntp.conf-gentoo.erb"
      $server = [
        '0.gentoo.pool.ntp.org',
        '1.gentoo.pool.ntp.org',
        '2.gentoo.pool.ntp.org',
        '3.gentoo.pool.ntp.org',
      ]
      $restrict = [
        'default nomodify nopeer',
      ]
    }
    'RedHat-7': {
      $package_name = 'chrony'
      $service_name = 'chronyd'
      $config_file = '/etc/chrony.conf'
      $template = "${module_name}/chrony.conf-rhel.erb"
      $server = [
        '0.rhel.pool.ntp.org iburst',
        '1.rhel.pool.ntp.org iburst',
        '2.rhel.pool.ntp.org iburst',
        '3.rhel.pool.ntp.org iburst',
      ]
      $restrict = undef
    }
    default: {
      $package_name = 'ntp'
      $service_name = 'ntpd'
      $config_file = '/etc/ntp.conf'
      $template = "${module_name}/ntp.conf-rhel.erb"
      $server = [
        '0.rhel.pool.ntp.org',
        '1.rhel.pool.ntp.org',
        '2.rhel.pool.ntp.org',
      ]
      $restrict = [
        'default kod nomodify notrap nopeer noquery',
        '-6 default kod nomodify notrap nopeer noquery',
      ]
    }
  }

}
#include '::ntp' NOTE(arjun): removed
