class autofs {
  include autofs::params

  package { $autofs::params::package:
    ensure => installed,
    notify => Service[$autofs::params::service],
  }

  service { $autofs::params::service:
    ensure  => running,
    enable  => true,
    require => Package[$autofs::params::package],
  }

}
