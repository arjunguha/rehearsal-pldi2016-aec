class mysql {
  package { [ "mysql-server", 'libmysql++-dev' ]:
    ensure => latest
  }

  service { "mysql":
    require => Package["mysql-server"],
    ensure => running,
    enable => true,
    hasrestart => true
  }

  exec { "Add ubuntu user":
    require => Service["mysql"],
    command => "mysql -uroot \
                --execute=\"GRANT ALL PRIVILEGES ON *.* TO 'ubuntu'@'%';\"",
    unless => "mysql -uroot --batch --skip-column-names \
               --execute=\"SELECT User FROM mysql.user WHERE User = 'ubuntu' AND Host = '%';\" | grep -q ubuntu"
  }

  augeas  { "bind address":
    notify => Service["mysql"],
    context => "/files/etc/mysql/my.cnf",
    changes => "set /files/etc/mysql/my.cnf/target[. = 'mysqld']/bind-address 0.0.0.0"
  }

  if $::ec2_ami_id and "xvdf1" in $::lsblk {
    file { "/var/lib/mysql":
      ensure => directory
    } ->
    mount { "/var/lib/mysql":
      before => Package["mysql-server"],
      ensure => mounted,
      atboot => true,
      device => "/dev/xvdf1",
      fstype => "xfs",
      options => "noatime,noexec,nodiratime",
      dump => 0,
      pass => 0
    }
  }
}
