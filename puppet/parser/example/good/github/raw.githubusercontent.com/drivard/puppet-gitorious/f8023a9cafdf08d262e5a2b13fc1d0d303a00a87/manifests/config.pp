class gitorious::config {
  # Configure MySQL
  $server = $gitorious::mysql_server
  $pwd = $gitorious::mysql_pwd
  $git_pwd = $gitorious::git_database_password
  $email = $gitorious::webmaster_email
  $git_email = $gitorious::gitorious_email
  $sendmail_domain = $gitorious::sendmail_domain
  $git_fqdn = $gitorious::git_fqdn

  # Gitorious folders
  $gitorious_folders = ["/var/www/gitorious/tmp/pids","/var/www/gitorious/tarballs-work","/var/www/gitorious/tarballs","/var/www/gitorious/repositories"]

  file {
    "/usr/src/create_database.sh":
      owner   => "root",
      group   => "root",
      mode    => "0755",
      ensure  => file,
      content => template("gitorious/mysql/create_database.sh.erb");

    "/usr/local/bin/ruby":
      ensure  => link,
      target  => "/opt/ruby-enterprise/bin/ruby";

    "/usr/local/bin/rake":
      ensure  => link,
      target  => "/opt/ruby-enterprise/bin/rake";

    "/usr/local/bin/bundle":
      ensure  => link,
      target  => "/opt/ruby-enterprise/bin/bundle";

    "/usr/local/sphinx":
      ensure  => link,
      target  => "/usr/local/sphinx-2.0.3-release";

    "/usr/local/bin/indexer":
      ensure  => link,
      target  => "/usr/local/sphinx/bin/indexer",
      require => [File["/usr/local/sphinx"],];

    "/usr/local/bin/indextool":
      ensure  => link,
      target  => "/usr/local/sphinx/bin/indextool",
      require => [File["/usr/local/sphinx"],];

    "/usr/local/bin/search":
      ensure  => link,
      target  => "/usr/local/sphinx/bin/search",
      require => [File["/usr/local/sphinx"],];

    "/usr/local/bin/searchd":
      ensure  => link,
      target  => "/usr/local/sphinx/bin/searchd",
      require => [File["/usr/local/sphinx"],];

    "/usr/local/bin/spelldump":
      ensure  => link,
      target  => "/usr/local/sphinx/bin/spelldump",
      require => [File["/usr/local/sphinx"],];

    "/etc/init.d/git-poller":
      owner   => 'root',
      group   => 'root',
      mode    => '0755',
      ensure  => file,
      source  => "puppet:///modules/gitorious/scripts/git-poller";

    "/etc/init.d/git-ultrasphinx":
      owner   => 'root',
      group   => 'root',
      mode    => '0755',
      ensure  => file,
      source  => "puppet:///modules/gitorious/scripts/git-ultrasphinx";

    "/etc/init.d/git-daemon":
      owner   => 'root',
      group   => 'root',
      mode    => '0755',
      ensure  => file,
      source  => "puppet:///modules/gitorious/scripts/git-daemon";

    "/etc/init.d/activemq":
      owner   => 'root',
      group   => 'root',
      mode    => '0755',
      ensure  => file,
      source  => "puppet:///modules/gitorious/scripts/activemq";
      
    # Make this file a template for future enhancement
    "/etc/default/activemq":
      owner   => 'root',
      group   => 'root',
      mode    => '0600',
      ensure  => file,
      content => template("gitorious/activemq/activemq.erb");
      
    "/usr/local/apache-activemq/conf/activemq.xml":
      owner   => 'activemq',
      group   => 'nogroup',
      mode    => '0644',
      ensure  => file,
      source  => "puppet:///modules/gitorious/config/activemq/activemq.xml";

    "/usr/local/bin/gitorious":
      ensure  => link,
      target  => "/var/www/gitorious/script/gitorious";

    "/etc/logrotate.d/gitorious":
      ensure  => link,
      target  => "/var/www/gitorious/doc/templates/ubuntu/gitorious-logrotate";

    "/etc/apache2/mods-available/passenger.load":
      owner   => 'root',
      group   => 'root',
      mode    => '0644',
      ensure  => file,
      source  => "puppet:///modules/gitorious/config/apache/passenger.load";

    "/etc/apache2/sites-available/gitorious":
      owner   => 'root',
      group   => 'root',
      mode    => '0644',
      ensure  => file,
      content => template("gitorious/vhosts/gitorious");

    "/etc/apache2/sites-available/gitorious-ssl":
      owner   => 'root',
      group   => 'root',
      mode    => '0644',
      ensure  => file,
      content => template("gitorious/vhosts/gitorious-ssl");

    "/var/www/gitorious/.ssh":
      owner   => 'git',
      group   => 'git',
      mode    => '0700',
      ensure  => directory;

    "/var/www/gitorious/.ssh/authorized_keys":
      owner   => 'git',
      group   => 'git',
      mode    => '0600',
      ensure  => file,
      require => [File["/var/www/gitorious/.ssh"],];

    $gitorious_folders:
      owner   => 'git',
      group   => 'git',
      mode    => '0755',
      ensure  => directory;

    "/var/www/gitorious/log/production.log":
      owner   => 'git',
      group   => 'git',
      mode    => '0666',
      ensure  => file;

    "/usr/src/gitorious.yml":
      owner   => 'git',
      group   => 'git',
      mode    => '0644',
      content => template("gitorious/rails/gitorious.yml.erb");

    "/var/www/gitorious/config/database.yml":
      owner   => 'git',
      group   => 'git',
      mode    => '0644',
      content => template("gitorious/rails/database.yml.erb");

    "/var/www/gitorious/config/broker.yml":
      owner   => 'git',
      group   => 'git',
      mode    => '0644',
      content => template("gitorious/rails/broker.yml.erb");

    "/etc/profile.d/gitorious.sh":
      owner   => 'root',
      group   => 'root',
      mode    => '0644',
      source  => "puppet:///modules/gitorious/config/gitorious.profile";

    "/etc/mail/genericsdomain":
      owner   => 'root',
      group   => 'root',
      mode    => '0644',
      content => template("gitorious/sendmail/genericsdomain");

    "/etc/mail/genericstable":
      owner   => 'root',
      group   => 'root',
      mode    => '0644',
      content => template("gitorious/sendmail/genericstable");

    "/etc/mail/gitorious.m4":
      owner   => 'root',
      group   => 'root',
      mode    => '0644',
      content => template("gitorious/sendmail/gitorious.m4");

    "/etc/mail/sendmail.mc":
      owner   => 'root',
      group   => 'root',
      mode    => '0644',
      source  => "puppet:///modules/gitorious/config/sendmail/sendmail.mc";

    # Fix missing requirements in boot.rb
    "/var/www/gitorious/config/boot.rb":
      owner   => 'git',
      group   => 'git',
      mode    => '0644',
      source  => "puppet:///modules/gitorious/rails/boot.rb";

    "/usr/src/gitorious_secret.sh":
      owner   => 'root',
      group   => 'root',
      mode    => '0755',
      source  => "puppet:///modules/gitorious/config/rails/gitorious_secret.sh",
      require => [File["/usr/src/gitorious.yml"],];
      
    "/var/www/gitorious/config/ultrasphinx/production.conf":
      owner   => 'git',
      group   => 'git',
      mode    => '0644',
      content => template("gitorious/rails/production.conf.erb"),
      require => [Exec["/usr/local/bin/bundle exec rake ultrasphinx:bootstrap"],];

    "/var/www/gitorious/script/git-daemon":
      owner   => 'git',
      group   => 'git',
      mode    => '0755',
      source  => "puppet:///modules/gitorious/rails/git-daemon";
      
    "/var/www/cron":
      owner   => 'git',
      group   => 'git',
      mode    => '0755',
      ensure  => directory;
      
    "/var/www/cron/gitorious.sh":
      owner   => 'git',
      group   => 'git',
      mode    => '0755',
      source  => "puppet:///modules/gitorious/config/cron/gitorious.sh",
      require => [File["/var/www/cron"],];
  }

  exec {
    "configure_mysql_database":
      command => "/bin/bash /usr/src/create_database.sh >> /usr/src/database_created.log 2>&1;",
      user    => "root",
      cwd     => "/usr/src",
      creates => "/usr/src/database_created.log",
      require => [File["/usr/src/create_database.sh"],];

    "update-rc.d memcached defaults":
      user    => "root",
      creates => "/var/lib/update-rc.d/memcached";

    "a2enmod passenger":
      user    => "root",
      creates => "/etc/apache2/mods-enabled/passenger.load",
      require => [File["/etc/apache2/mods-available/passenger.load"], ];

    "a2enmod rewrite":
      user    => "root",
      creates => "/etc/apache2/mods-enabled/rewrite.load";

    "a2enmod ssl":
      user    => "root",
      creates => "/etc/apache2/mods-enabled/ssl.load";

    "a2enmod xsendfile":
      user    => "root",
      creates => "/etc/apache2/mods-enabled/xsendfile.load";

    "a2dissite default":
      user    => "root",
      onlyif => "test -f /etc/apache2/sites-enabled/000-default";

    "a2dissite default-ssl":
      user    => "root",
      onlyif => "test -f /etc/apache2/sites-enabled/default-ssl";

    "a2ensite gitorious":
      user    => "root",
      require => [File["/etc/apache2/sites-available/gitorious"],],
      unless  => "test -f /etc/apache2/sites-enabled/gitorious";

    "a2ensite gitorious-ssl":
      user    => "root",
      require => [File["/etc/apache2/sites-available/gitorious-ssl"],],
      unless  => "test -f /etc/apache2/sites-enabled/gitorious-ssl";

    "su -l git -c 'git submodule update --init' >> /usr/src/git_init.log 2>&1;":
      user    => "root",
      creates => "/usr/src/git_init.log",
      require => [Exec["chown -R git:git /var/www/gitorious"],Exec['chmod -R go-rwx /var/www/gitorious/.ssh'],];

    "chmod -R go-rwx /var/www/gitorious/.ssh":
      user        => "root",
      refreshonly => true,
      subscribe   => [File["/var/www/gitorious/.ssh/authorized_keys"],],
      require     => [File["/var/www/gitorious/.ssh/authorized_keys"],];

    "chown -R git:git /var/www/gitorious":
      user        => "root",
      refreshonly => true,
      subscribe   => [File[$gitorious_folders],],
      require     => [File[$gitorious_folders],];
      
    "chown -R activemq:nogroup /usr/local/apache-activemq-5.5.1":
      user        => "root",
      refreshonly => true,
      subscribe   => [File["/usr/local/apache-activemq/conf/activemq.xml"],],
      require     => [File["/usr/local/apache-activemq/conf/activemq.xml"],];

    "/usr/local/bin/bundle pack":
      command     => "su -l git -c '/usr/local/bin/bundle pack'",
      user        => "root",
      refreshonly => true,
      subscribe   => [Exec["clone_gitorious"],],
      require     => [Exec["gitorious_yml_secret"],File["/etc/profile.d/gitorious.sh"],Exec["chown -R git:git /var/www/gitorious"],Exec["chmod -R go-rwx /var/www/gitorious/.ssh"],File["/var/www/gitorious/config/boot.rb"],];

    "/usr/local/bin/bundle exec rake db:migrate":
      command     => "su -l git -c '/usr/local/bin/bundle exec rake db:migrate RAILS_ENV=production'",
      user        => "root",
      refreshonly => true,
      subscribe   => [Exec["/usr/local/bin/bundle pack"],],
      require     => [Exec["/usr/local/bin/bundle pack"],];

    "/usr/local/bin/bundle exec rake ultrasphinx:bootstrap":
      command     => "su -l git -c '/usr/local/bin/bundle exec rake ultrasphinx:bootstrap RAILS_ENV=production'",
      refreshonly => true,
      subscribe   => [Exec["/usr/local/bin/bundle pack"],],
      require     => [Exec["/usr/local/bin/bundle exec rake db:migrate"],];
      
    "/usr/local/bin/bundle exec rake ultrasphinx:index":
      command     => "su -l git -c '/usr/local/bin/bundle exec rake ultrasphinx:index RAILS_ENV=production'",
      refreshonly => true,
      subscribe   => [Exec["/usr/local/bin/bundle exec rake ultrasphinx:bootstrap"],],
      require     => [Exec["/usr/local/bin/bundle exec rake ultrasphinx:bootstrap"],];

    "m4 /etc/mail/sendmail.mc > /etc/mail/sendmail.cf":
      unless  => "test -f /etc/mail/genericstable.db",
      require => [File["/etc/mail/genericsdomain"],File["/etc/mail/gitorious.m4"],File["/etc/mail/sendmail.mc"],File["/etc/mail/genericstable"],];

    "makemap -r hash /etc/mail/genericstable.db < /etc/mail/genericstable":
      unless  => "test -f /etc/mail/genericstable.db",
      require => [Exec["m4 /etc/mail/sendmail.mc > /etc/mail/sendmail.cf"],];

    "gitorious_yml_secret":
      command => "sh /usr/src/gitorious_secret.sh",
      creates => "/var/www/gitorious/config/gitorious.yml.old",
      user    => "root",
      require => [File["/var/www/gitorious/config/boot.rb"],File["/usr/src/gitorious_secret.sh"],];
  }

  cron {
    "git_cron_1":
      command   => "/var/www/cron/gitorious.sh",
      user      => "git",
      hour      => '*',
      minute    => '*',
      month     => '*',
      monthday  => '*',
      weekday   => '*',
      require   => [Exec["/usr/local/bin/bundle exec rake ultrasphinx:bootstrap"],File["/var/www/cron/gitorious.sh"],];
  }
}
