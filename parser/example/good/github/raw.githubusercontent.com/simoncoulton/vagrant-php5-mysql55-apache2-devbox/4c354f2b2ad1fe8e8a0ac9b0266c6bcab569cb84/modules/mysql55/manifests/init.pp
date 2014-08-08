group { 'puppet': ensure => 'present' }

class mysql55 {
  package { [
    "mysql-server-5.5"
  ] :
    ensure => latest,
    require => Exec["apt-get update"]
  }
}