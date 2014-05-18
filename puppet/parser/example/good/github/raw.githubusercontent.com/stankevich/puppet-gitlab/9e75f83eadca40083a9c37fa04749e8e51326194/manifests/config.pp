class gitlab::config {

  group { 'git':
    ensure => present,
    gid    => '2001',
  }

  user { 'git':
    ensure     => present,
    comment    => 'Gitolite',
    uid        => '2001',
    gid        => '2001',
    shell      => '/bin/sh',
    home       => $gitlab::params::gitolite_dir,
    managehome => true,
  }

  user { 'gitlab':
    ensure     => present,
    comment    => 'Gitlab',
    system     => true,
    gid        => '2001',
    shell      => '/bin/sh',
    home       => $gitlab::params::gitlab_dir,
    managehome => true,
  }

  # Generating Gitlab SSH keypair
  exec { 'gitlab_gen_ssh_key':
    command     => "mkdir -p ${gitlab::params::gitlab_dir}/.ssh && \
      chmod 700 ${gitlab::params::gitlab_dir}/.ssh && \
      ssh-keygen -q -N '' -t rsa -f ${gitlab::params::gitlab_dir}/.ssh/id_rsa",
    creates     => "${gitlab::params::gitlab_dir}/.ssh/id_rsa",
    cwd         => $gitlab::params::gitlab_dir,
    user        => 'gitlab',
    group       => 'git',
    environment => "HOME=${gitlab::params::gitlab_dir}",
    notify      => Exec['gitlab_dist_ssh_key'],
  }

  # Copying Gitlab SSH keypair to Gitolite
  exec { 'gitlab_dist_ssh_key':
    command     => "cp -pr ${gitlab::params::gitlab_dir}/.ssh/id_rsa.pub \
      ${gitlab::params::gitolite_dir}/gitlab.pub && \
      chmod 640 ${gitlab::params::gitolite_dir}/gitlab.pub",
    refreshonly => true,
  }

  file { "${gitlab::params::gitolite_dir}/.gitolite.rc":
    ensure  => present,
    mode    => '0640',
    owner   => 'git',
    group   => 'git',
    source  => 'puppet:///modules/gitlab/gitolite.rc',
    notify  => Exec['gitolite_setup'],
    require => Exec['gitlab_dist_ssh_key'],
  }

  # Setting up Gitolite
  exec { 'gitolite_setup':
    command     => "gl-setup -q ${gitlab::params::gitolite_dir}/gitlab.pub",
    refreshonly => true,
    cwd         => $gitlab::params::gitolite_dir,
    user        => 'git',
    group       => 'git',
    environment => "HOME=${gitlab::params::gitolite_dir}",
    notify      => Exec['gitlab_permissions'],
  }

  # Fixing Gitolite permissions
  exec { 'gitlab_permissions':
    command     => "chmod -R g+rwX \
      ${gitlab::params::gitolite_dir}/repositories && \
      chown -R git:git ${gitlab::params::gitolite_dir}/repositories",
    refreshonly => true,
    notify      => Exec['gitlab_ssh_known_hosts'],
  }

  # Initializing known_hosts for Gitlab
  exec { 'gitlab_ssh_known_hosts':
    command     => 'ssh -o StrictHostKeyChecking=no git@localhost info',
    refreshonly => true,
    cwd         => $gitlab::params::gitlab_dir,
    user        => 'gitlab',
    group       => 'git',
    environment => "HOME=${gitlab::params::gitlab_dir}",
  }

  # Cloning Gitlab repo
  exec { 'gitlab_install':
    command     => 'git clone git://github.com/gitlabhq/gitlabhq.git gitlab',
    creates     => "${gitlab::params::gitlab_dir}/gitlab/config.ru",
    cwd         => $gitlab::params::gitlab_dir,
    user        => 'gitlab',
    group       => 'git',
    environment => "HOME=${gitlab::params::gitlab_dir}",
    notify      => Exec['gitlab_bundle'],
    require     => Exec['gitlab_ssh_known_hosts'],
  }

  # Gitlab config
  file { "${gitlab::params::gitlab_dir}/gitlab/config/gitlab.yml":
    ensure  => present,
    mode    => '0644',
    owner   => 'gitlab',
    group   => 'git',
    content => template('gitlab/gitlab.yml.erb'),
    notify  => Service['gitlab'],
    require => Exec['gitlab_install'],
  }

  # DB config
  file { "${gitlab::params::gitlab_dir}/gitlab/config/database.yml":
    ensure  => present,
    mode    => '0644',
    owner   => 'gitlab',
    group   => 'git',
    content => template('gitlab/database.yml.erb'),
    notify  => Service['gitlab'],
    require => Exec['gitlab_install'],
  }

  # Unicorn config
  file { "${gitlab::params::gitlab_dir}/gitlab/config/unicorn.rb":
    ensure  => present,
    mode    => '0644',
    owner   => 'gitlab',
    group   => 'git',
    content => template('gitlab/unicorn.rb.erb'),
    notify  => Service['gitlab'],
    require => Exec['gitlab_install'],
  }

  # LDAP
  file { "${gitlab::params::gitlab_dir}/gitlab/config/initializers/omniauth.rb":
    ensure  => present,
    mode    => '0644',
    owner   => 'gitlab',
    group   => 'git',
    content => template('gitlab/omniauth.rb.erb'),
    notify  => Service['gitlab'],
    require => Exec['gitlab_install'],
  }

  # Installing Gems
  exec { 'gitlab_bundle':
    command     => 'bundle install --without development test --deployment',
    refreshonly => true,
    cwd         => "${gitlab::params::gitlab_dir}/gitlab",
    user        => 'gitlab',
    group       => 'git',
    environment => "HOME=${gitlab::params::gitlab_dir}",
    require     => Exec['gitlab_install'],
  }

  # Initializing DB
  exec { 'gitlab_db':
    command     => 'bundle exec rake gitlab:app:setup RAILS_ENV=production',
    creates     => "${gitlab::params::gitlab_dir}/gitlab/.setup",
    cwd         => "${gitlab::params::gitlab_dir}/gitlab",
    user        => 'gitlab',
    group       => 'git',
    environment => "HOME=${gitlab::params::gitlab_dir}",
    notify      => Exec['gitlab_verify'],
    require     => [
      Exec['gitlab_bundle'],
      File["${gitlab::params::gitlab_dir}/gitlab/config/gitlab.yml"],
      File["${gitlab::params::gitlab_dir}/gitlab/config/database.yml"]
    ],
  }

  # Verifying setup
  exec { 'gitlab_verify':
    command     => "bundle exec rake gitlab:app:status RAILS_ENV=production && \
      echo > ${gitlab::params::gitlab_dir}/gitlab/.setup",
    refreshonly => true,
    cwd         => "${gitlab::params::gitlab_dir}/gitlab",
    user        => 'gitlab',
    group       => 'git',
    environment => "HOME=${gitlab::params::gitlab_dir}",
  }

}
