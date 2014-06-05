class phpmyadmin (
    $mysqlusername = "root",
    $mysqlpassword = "root",
    $webserver = "nginx"
){

    include phpmyadmin::ppa

    Class['phpmyadmin::ppa']->Class['phpmyadmin']

    package {
        "phpmyadmin":
            ensure  => present,
            require => [
                Exec['update-apt'],
                Package["php5", $webserver, "mysql-server"],
            ];
    }

    exec {
        "extract-pma-tables":
            cwd     => '/usr/share/doc/phpmyadmin/examples/',
            command => 'gunzip create_tables.sql.gz',
            require => Package['phpmyadmin'],
            creates => '/usr/share/doc/phpmyadmin/examples/create_tables.sql',
            notify  => Exec['install-pma-tables'];

        "install-pma-tables":
            cwd     => '/usr/share/doc/phpmyadmin/examples/',
            command => "mysql -u$mysqlusername -p$mysqlpassword < create_tables.sql",
            notify  => Exec['grant-access'],
            refreshonly => true;

        "grant-access":
            cwd     => '/usr/share/doc/phpmyadmin/examples/',
            command => "mysql -u$mysqlusername -p$mysqlpassword -e 'GRANT SELECT, INSERT, DELETE, UPDATE ON phpmyadmin.* TO 'pma'@'localhost' IDENTIFIED BY \"pmapassword\"'",
            refreshonly => true;
    }

    file {
        "/etc/phpmyadmin/config.inc.php":
            ensure => file,
            mode   => "0644",
            require=> Package['phpmyadmin'],
            source => 'puppet:///modules/phpmyadmin/config.inc.php';

        "/etc/phpmyadmin/config-db.php":
            ensure => file,
            mode   => '0644',
            source => 'puppet:///modules/phpmyadmin/config-db.php',
            require=> Package[$webserver];
    }


    if ($webserver == "nginx") {
        file {
            "/etc/nginx/conf.d/global/30-phpmyadmin.conf":
                ensure => file,
                mode   => '0644',
                source => "puppet:///modules/phpmyadmin/nginx-pma.conf",
                require=> Package["phpmyadmin", "nginx"];
        }
    }

    if ($webserver == "apache2") {
        file {
            "/etc/apache2/sites-available/phpmyadmin":
                ensure => file,
                mode   => '0644',
                source => "puppet:///modules/phpmyadmin/apache-pma.conf",
                require=> Package["phpmyadmin", "nginx"];

            "/etc/apache2/sites-enabled/phpmyadmin":
                ensure => link,
                mode   => '0644',
                target => "/etc/apache2/sites-available/phpmyadmin",
                require=> File["/etc/apache2/sites-available/phpmyadmin"];
        }
    }
}