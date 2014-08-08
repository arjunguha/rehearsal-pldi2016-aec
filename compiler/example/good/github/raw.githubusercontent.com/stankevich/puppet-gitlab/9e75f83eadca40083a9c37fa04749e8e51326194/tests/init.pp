class { 'gitlab':
  url            => 'git.example.com',
  emailfrom      => 'Gitlab <gitlab@example.com>',
  mysql_host     => 'db.example.com',
  mysql_db       => 'gitlab',
  mysql_user     => 'gitlab',
  mysql_pass     => 'password',
  ldap_host      => 'ad.example.com',
  ldap_base      => 'CN=Users,DC=ad,DC=example,DC=com',
  ldap_bind_user => 'CN=BindDN,OU=Service Accounts,DC=ad,DC=example,DC=com',
  ldap_bind_pass => 'password',
}
