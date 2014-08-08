class apache2 {

    # Apache Paket installieren
    package { "apache2":
        ensure => present,
    }

    # Zusätzliche Apache Tools installieren
    package { "apache2-utils":
        ensure => present,
        require => Package["apache2"]
    }

    # Sicherstellen, dass der Ordner web existiert
    file { "/vagrant/web":
        ensure => "directory",
    }

    # Apache Service starten
    service { "apache2":
        ensure => running,
        require => Package["apache2"]
    }

    # Konfiguration für Site schreiben
    file { "create-site":
      path    => "/etc/apache2/sites-available/default",
      ensure  => file,
      require => Package["apache2"],
      notify  => Service["apache2"],
      source  => "/tmp/vagrant-puppet/modules-0/apache2/files/default-site",
    }

    # Konfiguration für Site aktivieren
    exec { "enable-site":
    unless  => "test -f /etc/apache2/sites-enabled/000-default",
    command => "sudo a2ensite default",
    require => [Package["apache2"], File['/etc/apache2/sites-available/default']],
    notify  => Service["apache2"]
    }

    # mod_rewrite aktivieren
    exec { "enable-rewrite":
    unless  => "test -f /etc/apache2/mods-enabled/rewrite.load",
    command => "sudo a2enmod rewrite",
    notify  => Service["apache2"]
    }
}