class nginx {
  exec { "Register ppa:nginx/stable":
    require => Package["python-software-properties"],
    command => "apt-add-repository ppa:nginx/stable -y &&
                apt-get update",
    creates => "/etc/apt/sources.list.d/nginx-stable-${::lsbdistcodename}.list",
  } ->
  package { "nginx":
    ensure => latest
  }

  file { "/srv/www":
    require => Package['nginx'],
    ensure => directory,
    owner => "www-data",
    group => "www-data",
    mode => 0755,
    recurse => true
  } ->
  user { "ubuntu":
    groups => "www-data"
  }

  service { "nginx":
    require => Package['nginx'],
    ensure => running,
    enable => true,
    hasrestart => true
  }

  file { "/etc/nginx/nginx.conf":
    require => Package['nginx'],
    notify => Service["nginx"],
    ensure => present,
    owner => "root",
    group => "root",
    mode => 0644,
    source => "puppet:///modules/nginx/nginx.conf"
  } ->
  file { "/etc/nginx/sites-enabled/default":
    notify => Service["nginx"],
    ensure => absent
  }

  if $::ec2_ami_id and "xvdg1" in $::lsblk {
    mount { "/srv/www":
      require => File["/srv/www"],
      ensure => mounted,
      atboot => true,
      device => "/dev/xvdg1",
      fstype => "ext4",
      options => "noatime,noexec,nodiratime",
      dump => 0,
      pass => 0
    }
  }
}
