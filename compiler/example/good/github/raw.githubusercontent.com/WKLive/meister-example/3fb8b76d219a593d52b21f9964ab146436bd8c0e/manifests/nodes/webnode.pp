node application1 inherits basenode {
  class { 'apache': }
  class { 'php': }
  class { 'drush': }
  class { 'postfix': }
  class { 'puppet::agent':
    server => "mgmt.fabsorize.me",
    certname => "application1"
  }
  class { 'aegir::slave': }
  class { 'mysql':
    hostname => 'application1',
    local_only     => false,
    create_aegir_user => true,
    aegir_user     => 'aegir',
    aegir_password => 'a_sillyPassword',
    aegir_host     => '%'
  }
}
