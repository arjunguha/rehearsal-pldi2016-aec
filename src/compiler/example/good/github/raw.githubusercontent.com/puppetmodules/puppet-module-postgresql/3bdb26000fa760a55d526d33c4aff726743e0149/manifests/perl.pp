class postgresql::perl {
  package { 'libdbd-pg-perl':
    ensure => present,
  }
}
