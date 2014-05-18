# == Class: gitlab
#
# Installs and manages Gitlab.
#
# === Notes
#
# Requires "ruby1.9.3" package in available repository.
#
# === Parameters
#
# [*url*]
#  Gitlab URL to use in emails. Default: FQDN
#
# [*email*]
#  From: email address to use for sending out notifications.
#  Default: Gitlab <gitlab@FQDN>
#
# [*mysql_host*]
#  MySQL hostname. Default: localhost
#
# [*mysql_db*]
#  MySQL DB name. Default: gitlab
#
# [*mysql_user*]
#  MySQL username. Default: gitlab
#
# [*mysql_pass*]
#  MySQL password. Default: gitlab
#
# [*ldap_host*]
#  LDAP server. Default: disabled
#
# [*ldap_base*]
#  LDAP base DN.
#
# [*ldap_bind_user*]
#  LDAP binding DN.
#
# [*ldap_bind_pass*]
#  LDAP binding DN password.
#
# === Examples
#
# class { 'gitlab':
#   url            => 'git.example.com',
#   emailfrom      => 'Gitlab <gitlab@example.com>',
#   mysql_host     => 'db.example.com',
#   mysql_db       => 'gitlab',
#   mysql_user     => 'gitlab',
#   mysql_pass     => 'password',
#   ldap_host      => 'ad.example.com',
#   ldap_base      => 'CN=Users,DC=ad,DC=example,DC=com',
#   ldap_bind_user => 'CN=BindDN,OU=Service Accounts,DC=ad,DC=example,DC=com',
#   ldap_bind_pass => 'password',
# }
#
# === Authors
#
# Sergey Stankevich
#
class gitlab (
  $url             = $::fqdn,
  $email           = "Gitlab <gitlab@${::fqdn}>",
  $mysql_host      = 'localhost',
  $mysql_db        = 'gitlab',
  $mysql_user      = 'gitlab',
  $mysql_pass      = 'gitlab',
  $ldap_host       = false,
  $ldap_base       = false,
  $ldap_bind_user  = false,
  $ldap_bind_pass  = false
) {

  # Compatibility check
  $compatible = [ 'Debian', 'Ubuntu' ]
  if ! ($::operatingsystem in $compatible) {
    fail("Module is not compatible with ${::operatingsystem}")
  }

  Class['gitlab::install'] -> Class['gitlab::config']
  Class['gitlab::config']  -> Class['gitlab::service']

  include gitlab::params
  include gitlab::install
  include gitlab::config
  include gitlab::service

}
