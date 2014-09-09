class gitorious
(
  $mysql_server = '127.0.0.1',
  $mysql_pwd    = 'gitorious',
  $git_database_password = 'g1t0r1Ou5',
  $webmaster_email = 'webmaster@localhost',
  $gitorious_email = 'noreply@example.com',
  $sendmail_domain = 'example.com',
  $git_fqdn = 'gitorious.example.com'
)
{
  exec {
    "apt-get update":;
    "apt-get upgrade -y":
      require => [Exec["apt-get update"],];
    "apt-get dist-upgrade -y":
      require => [Exec["apt-get upgrade -y"],];
      
    "adduser_git":
      command => "adduser --system --home /var/www/gitorious --no-create-home --group --shell /bin/bash git",
      user    => "root",
      unless  => "grep -c '^git:' /etc/passwd",
      timeout => 0;
      
    "adduser_activemq":
      command => "adduser --system --no-create-home --home /usr/local/apache-activemq --shell /bin/bash activemq",
      user    => "root",
      unless  => "grep -c '^activemq:' /etc/passwd",
      timeout => 0;
  }
  
  # List of packages that will be install on each node
  $package_list = [
    "sudo",
    "build-essential",
    "sendmail",
    "sendmail-bin",
    "make",
    "zlib1g",
    "zlib1g-dev",
    "ssh",
    "libssl-dev",
    "apache2",
    "mysql-client",
    "mysql-server",
    "apg",
    "geoip-bin",
    "libgeoip1",
    "libgeoip-dev",
    "libpcre3",
    "libpcre3-dev",
    "libyaml-dev",
    "libmysqlclient-dev",
    "apache2-threaded-dev",
    "libonig-dev",
    "zip",
    "unzip",
    "memcached",
    "git-core",
    "git-svn",
    "git-doc",
    "git-cvs",
    "libreadline-dev",
    "openjdk-6-jre",
    "sqlite3",
    "libsqlite3-dev",
    "libmagick++3",
    "libmagick++-dev",
    "libapache2-mod-xsendfile",
    "libxslt1-dev",
    "libcurl4-openssl-dev",
    "uuid",
    "uuid-dev",
    "libaspell-dev",
  ]

  file {
    "/usr/src/gitorious-packages":
      owner   => "root",
      group   => "root",
      mode    => "755",
      ensure  => directory;

    "/usr/src/gitorious-packages/ruby-enterprise-1.8.7-2012.02.tar.gz":
      owner   => "root",
      group   => "root",
      mode    => "755",
      source  => "puppet:///modules/gitorious/tarballs/ruby-enterprise-1.8.7-2012.02.tar.gz",
      require => [File['/usr/src/gitorious-packages'],];

    "/usr/src/gitorious-packages/apache-activemq-5.5.1-bin.tar.gz":
      owner   => "root",
      group   => "root",
      mode    => "755",
      source  => "puppet:///modules/gitorious/tarballs/apache-activemq-5.5.1-bin.tar.gz",
      require => [File['/usr/src/gitorious-packages'],];

    "/usr/src/gitorious-packages/sphinx-2.0.3-release.tar.gz":
      owner   => "root",
      group   => "root",
      mode    => "755",
      source  => "puppet:///modules/gitorious/tarballs/sphinx-2.0.3-release.tar.gz",
      require => [File['/usr/src/gitorious-packages'],];
  }

  include gitorious::install, gitorious::config, gitorious::service

  # Module Dependencies
  Class['gitorious'] -> Class['gitorious::install'] -> Class['gitorious::config'] -> Class['gitorious::service']
  Class['gitorious::config'] ~> Class['gitorious::service']
}
