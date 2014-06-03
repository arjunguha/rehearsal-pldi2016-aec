class gitlab::install {

  package { 'gitolite': ensure => present }

  package { [ 'wget', 'gcc', 'checkinstall'             ]: ensure => present }
  package { [ 'libxml2-dev', 'libxslt1-dev', 'sqlite3'  ]: ensure => present }
  package { [ 'libsqlite3-dev', 'libcurl4-openssl-dev'  ]: ensure => present }
  package { [ 'libreadline-dev', 'libc6-dev'            ]: ensure => present }
  package { [ 'libssl-dev', 'libmysql++-dev', 'make'    ]: ensure => present }
  package { [ 'zlib1g-dev', 'libicu-dev', 'libyaml-0-2' ]: ensure => present }
  package { [ 'libyaml-dev', 'python-dev', 'python-pip' ]: ensure => present }
  package { [ 'mysql-client', 'libmysqlclient-dev'      ]: ensure => present }
  package { [ 'ruby1.9.3'                               ]: ensure => present }

  package { 'Pygments':
    ensure   => present,
    provider => 'pip',
    require  => Package['python-pip'],
  }

  package { 'bundler':
    ensure   => present,
    provider => 'gem',
    require  => Package['ruby1.9.3'],
  }

}
