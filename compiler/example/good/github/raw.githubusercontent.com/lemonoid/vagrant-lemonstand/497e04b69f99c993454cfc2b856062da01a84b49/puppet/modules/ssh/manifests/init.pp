class ssh
{
  $packages = [
    "openssh-server",
    "openssh-client",
  ]

  package { $packages:
    ensure  => latest,
    require => Exec['apt-get update']
  }

  service { "ssh":
    ensure    => running,
    enable    => true,
    require   => Package[$packages],
  }

  file { "/home/vagrant/.ssh":
    ensure => directory,
    mode   => 0700,
    owner  => "vagrant",
    group  => "vagrant",
  }

  file { "/home/vagrant/.ssh/config":
    ensure  => present,
    mode    => 0600,
    owner   => "vagrant",
    group   => "vagrant",
    require => File["/home/vagrant/.ssh"],
  }

  file {"/home/vagrant/.ssh/authorized_keys":
    ensure => present,
    mode   => 0600,
    owner  => "vagrant",
    group  => "vagrant",
    require => File["/home/vagrant/.ssh"],
  }

  exec { "add ssh keys": 
    command => "/bin/cp /srv/config/id_rsa /home/vagrant/.ssh/id_rsa",
    onlyif  => "test -f /srv/config/id_rsa",
    # unless  => "test -f /home/vagrant/.ssh/id_rsa",
    require => File["/home/vagrant/.ssh"],
  }

  file {"/home/vagrant/.ssh/id_rsa":
    ensure => file,
    mode   => 0600,
    owner  => "vagrant",
    group  => "vagrant",
    require => Exec["add ssh keys"],
  }

  exec { "add authorized keys": 
    command => "/bin/cat /srv/config/authorized_keys >> /home/vagrant/.ssh/authorized_keys",
    onlyif  => "test -f /srv/config/authorized_keys",
    # unless  => "test -f ~/.ssh/known_hosts",
    require => File["/home/vagrant/.ssh"],
  }

  $known_hosts = $params::ssh_known_hosts

  file { "/home/vagrant/.ssh/known_hosts":
    ensure  => present,
    mode    => 0600,
    owner   => "vagrant",
    group   => "vagrant",
    content => template("ssh/known_hosts.erb"),
    # unless => "grep ${known_hosts} /home/vagrant/.ssh/known_hosts"
    require => File["/home/vagrant/.ssh"]
  }

  # exec { "add knownhosts": 
  #   command => "/bin/cat /srv/config/known_hosts >> ~/.ssh/known_hosts",
  #   onlyif  => "test -f /srv/config/known_hosts",
  #   # unless  => "test -f ~/.ssh/known_hosts",
  #   require => Exec["verify directory"],
  # }

}
