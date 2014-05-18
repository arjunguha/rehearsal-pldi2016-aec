class git::client::install {
  package { $git::params::packagename:
    ensure => present,
  }
}

# vim:sw=2:ts=2:expandtab
