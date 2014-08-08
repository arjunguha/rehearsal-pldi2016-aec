class mysql {

   # MySQL Client und Server installieren
   package {
      ["mysql-client", "mysql-server", "libmysqlclient-dev"]: 
        ensure => installed, require => Exec['apt-get update'],
        notify  => Service['apache2']
    }

  # Sicherstellen, dass mysql läuft
  service { "mysql":
    ensure => running,
    require => Package["mysql-server"]
  }
}