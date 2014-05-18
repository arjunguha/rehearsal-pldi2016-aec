# The aegir master server.
class aegir::master (
  $hostmaster_url = 'master.example.com.',
  $email = 'admin@example.com',
  $db_host = 'localhost',
  $db_user = 'root',
  $db_password = '',
  # Some irrelevant git values (We will only pull, but git throws "errors" if we don't specify them).
  $git_username = 'ci',
  $git_email='ci@example.com'
  ) {

  # These variables can be used to provide default values for our aegir setup.
  exec {"/bin/echo /usr/bin/debconf aegir/site string $hostmaster_url | /usr/bin/debconf-set-selections": before  => Package['aegir'], }
  exec {"/bin/echo /usr/bin/debconf aegir/db_host string $db_host | /usr/bin/debconf-set-selections": before  => Package['aegir'], }
  exec {"/bin/echo /usr/bin/debconf aegir/db_user string $db_user | /usr/bin/debconf-set-selections": before  => Package['aegir'], }
  exec {"/bin/echo /usr/bin/debconf aegir/db_password string $db_password | /usr/bin/debconf-set-selections": before  => Package['aegir'], }
  exec {"/bin/echo /usr/bin/debconf aegir/email string $email | /usr/bin/debconf-set-selections": before  => Package['aegir'], }
  if $aegir_makefile {
    exec {"/bin/echo /usr/bin/debconf aegir/makefile string $aegir_makefile | /usr/bin/debconf-set-selections": before  => Package['aegir'], }
  }

  # Add the Aegir repository.
  file { "/etc/apt/sources.list.d/aegir.list":
    ensure => present,
    owner => root,
    content => 'deb http://debian.aegirproject.org stable main',
    mode => 0644,
  }
  exec { "aegir-add-repo-key":
    command => "/usr/bin/wget -q http://debian.aegirproject.org/key.asc -O- | /usr/bin/apt-key add -",
    require => File["/etc/apt/sources.list.d/aegir.list"],
  }
  # The Aegir user needs to be member of shadow, so that we can resolve user passwords.
  user { "aegir":
    ensure => "present",
    groups =>  ["www-data", "shadow"],
    require => Package['aegir']
  }
  package { "aegir-provision":
    ensure => latest,
  }

  package { "aegir":
    ensure => latest,
    require => [Package["aegir-provision"], Service["mysql"], Exec["mysql-remove-anonymous"]]
  }

  file { "/var/aegir/.ssh":
    ensure => directory,
    owner => 'aegir',
    require => Package['aegir']
  }

  file { '/var/aegir/.ssh/config':
    ensure => file,
    owner => 'aegir',
    group => 'aegir',
    mode => '0440',
    source => 'puppet:///modules/aegir/aegir_sshconfig',
    require => File["/var/aegir/.ssh"]
  }

  # This key will be used for logging in to the servers we are managing.
  file { "/var/aegir/.ssh/id_rsa":
    ensure => present,
    source => "puppet:///modules/aegir/keys/deploy",
    owner => 'aegir',
    mode => 400,
    require => [Package['aegir'], File["/var/aegir/.ssh"]]
  }
  file { "/var/aegir/.ssh/id_rsa.pub":
    ensure => present,
    source => "puppet:///modules/aegir/keys/deploy.pub",
    owner => 'aegir',
    mode => 400,
    require => [Package['aegir'], File["/var/aegir/.ssh"]]
  }
  # Create a git configuration.
  file { "/var/aegir/.gitconfig":
    content => template('jenkins/gitconfig.erb'),
    ensure => present,
    require => Package['aegir'],
    owner => 'aegir'
  }
  # Create a web root that can be managed by aegir.
  file { "/srv/www":
    ensure => directory,
    require => Package['aegir'],
    owner => 'aegir'
  }
  Package { require => Exec['apt-get update'] }
}
