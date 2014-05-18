class gitorious::install {
  package {
    $gitorious::package_list:
      ensure => present;

    "raspell":
      ensure    => present,
      provider  => "gem",
      require   => [Exec["yes '' | /usr/src/gitorious-packages/ruby-enterprise-1.8.7-2012.02/installer"],File["/usr/local/bin/gem"],];
  }

  exec {
    "tar zxf apache-activemq-5.5.1-bin.tar.gz":
      user    => "root",
      cwd     => "/usr/src/gitorious-packages/",
      unless  => "test -d /usr/src/gitorious-packages/apache-activemq-5.5.1";

    "tar zxf ruby-enterprise-1.8.7-2012.02.tar.gz":
      user    => "root",
      cwd     => "/usr/src/gitorious-packages/",
      unless  => "test -d /usr/src/gitorious-packages/ruby-enterprise-1.8.7-2012.02";

    "tar zxf sphinx-2.0.3-release.tar.gz":
      user    => "root",
      cwd     => "/usr/src/gitorious-packages/",
      unless  => "test -d /usr/src/gitorious-packages/sphinx-2.0.3-release";

    # Install Ruby Enterprise and Passenger
    "yes '' | /usr/src/gitorious-packages/ruby-enterprise-1.8.7-2012.02/installer":
      user    => "root",
      cwd     => "/usr/src/gitorious-packages/ruby-enterprise-1.8.7-2012.02/",
      creates => "/opt/ruby-enterprise-1.8.7-2012.02/bin/ruby",
      require => [Exec["tar zxf ruby-enterprise-1.8.7-2012.02.tar.gz"],Package[$gitorious::package_list],],
      timeout => 0;

    "yes '' | /opt/ruby-enterprise-1.8.7-2012.02/bin/passenger-install-apache2-module":
      user    => "root",
      cwd     => "/opt/ruby-enterprise-1.8.7-2012.02/",
      creates => "/opt/ruby-enterprise-1.8.7-2012.02/lib/ruby/gems/1.8/gems/passenger-3.0.11/ext/apache2/mod_passenger.so",
      require => [Exec["yes '' | /usr/src/gitorious-packages/ruby-enterprise-1.8.7-2012.02/installer"],],
      timeout => 0;

    # Install Sphinx
    "configure_sphinx":
      command => "sh configure --prefix=/usr/local/sphinx-2.0.3-release",
      user    => "root",
      cwd     => "/usr/src/gitorious-packages/sphinx-2.0.3-release",
      require => [Exec["tar zxf sphinx-2.0.3-release.tar.gz"],Package[$gitorious::package_list],],
      timeout => 0,
      unless  => "test -f /usr/local/sphinx-2.0.3-release/bin/searchd";

    "make_sphinx":
      command => "make",
      user    => "root",
      cwd     => "/usr/src/gitorious-packages/sphinx-2.0.3-release",
      require => [Exec["configure_sphinx"],],
      timeout => 0,
      unless  => "test -f /usr/local/sphinx-2.0.3-release/bin/searchd";

    "make_install_sphinx":
      command => "make install",
      user    => "root",
      cwd     => "/usr/src/gitorious-packages/sphinx-2.0.3-release",
      require => [Exec["make_sphinx"],],
      timeout => 0,
      unless  => "test -f /usr/local/sphinx-2.0.3-release/bin/searchd";

    "clone_gitorious":
      command => "git clone git://gitorious.org/gitorious/mainline.git /var/www/gitorious",
      user    => "root",
      unless  => "test -d /var/www/gitorious",
      timeout => 0,
      require => [Package[$gitorious::package_list],];

    # Install ActiveMQ
    "move-activemq-folder":
      command => "mv apache-activemq-5.5.1 /usr/local",
      user    => "root",
      cwd     => "/usr/src/gitorious-packages/",
      unless  => "test -d /usr/local/apache-activemq-5.5.1",
      timeout => 0,
      require => [Exec["tar zxf apache-activemq-5.5.1-bin.tar.gz"],];

    "activemq_setup":
      command => "/usr/local/apache-activemq/bin/activemq setup /etc/default/activemq >> /usr/src/activemq_setup.log",
      user    => "root",
      cwd     => "/usr/local/apache-activemq/bin",
      creates => "/usr/src/activemq_setup.log",
      timeout => 0,
      require => [File["/usr/local/apache-activemq"], ];

    "/opt/ruby-enterprise-1.8.7-2012.02/bin/bundle pack":
      user        => "root",
      cwd         => "/var/www/gitorious",
      refreshonly => true,
      subscribe   => [Exec["clone_gitorious"],],
      timeout     => 0,
      require     => [Exec["clone_gitorious"],Exec["yes '' | /opt/ruby-enterprise-1.8.7-2012.02/bin/passenger-install-apache2-module"],];

    "/opt/ruby-enterprise-1.8.7-2012.02/bin/bundle install":
      user        => "root",
      cwd         => "/var/www/gitorious",
      refreshonly => true,
      subscribe   => [Exec["/opt/ruby-enterprise-1.8.7-2012.02/bin/bundle pack"],],
      timeout     => 0,
      require     => [Exec["/opt/ruby-enterprise-1.8.7-2012.02/bin/bundle pack"], ];
  }

  file {
    "/usr/local/apache-activemq":
      ensure  => link,
      target  => "/usr/local/apache-activemq-5.5.1",
      require => [Exec["move-activemq-folder"],];
      
    "/usr/local/apache-activemq-5.5.1":
      owner   => 'activemq',
      group   => 'nogroup',
      mode    => '0755',
      ensure  => directory,
      require => [Exec["move-activemq-folder"],];
      
    "/opt/ruby-enterprise":
      ensure  => link,
      target  => "/opt/ruby-enterprise-1.8.7-2012.02/",
      require => [Exec["yes '' | /usr/src/gitorious-packages/ruby-enterprise-1.8.7-2012.02/installer"],];

    "/usr/local/bin/gem":
      ensure  => link,
      target  => "/opt/ruby-enterprise/bin/gem",
      require => [File["/opt/ruby-enterprise"],];
  }
}
