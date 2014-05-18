class mysql (
    $root_password = "root"
) inherits mysql::params {


    package {
        $pkg_name:
            ensure => latest,
            require=> Exec['update-apt'];
    }


    service {
        $svc_name:
            ensure  => running,
            enable  => true,
            require => Package[$pkg_name]
    }


    exec {
        "set-mysql-password":
            unless  => "mysqladmin -uroot -p$root_password status",
            command => "mysqladmin -uroot password $root_password",
            require => Service[$svc_name],
    }

    file {
        "/etc/mysql/conf.d/mysqld_default_utf8.cnf":
            ensure => file,
            mode   => "0644",
            require=> Package[$pkg_name],
            notify => Service[$svc_name],
            source => 'puppet:///modules/mysql/mysqld_default_utf8.cnf';
    }
}