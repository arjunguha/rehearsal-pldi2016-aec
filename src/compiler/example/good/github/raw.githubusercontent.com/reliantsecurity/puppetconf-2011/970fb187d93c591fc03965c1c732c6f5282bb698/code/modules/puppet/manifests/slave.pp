# = Class: puppet::slave
#
# == Descrition
#
# Creates a nginx/passenger Puppet slave
#
# == Module Dependencies
# - account
# - nginx
#
# This ssh keypair is site-specific
#
# To create a key:
# 1. cd modules/puppet/files/slave/sites/$my_site
# 2. ssh-keygen -t rsa -C "rsync@$my_site" -f id_rsa
# 3. Copy key into puppet::master
#
class puppet::slave {

	include puppet::client
	include puppet::passenger
	include puppet::accounts

	$rsync_user = "rsync${my_site}"
	account::user { $rsync_user: }

	# We need to include this in order to use qualified variables
	include account

	include packages
	Package <| title == rsync |>

	puppet::server {
		production:
			owner => $rsync_user,
			group => $rsync_user,
      require => Account::User[$rsync_user];
		trunk:
			rsync_minutes => [ 5, 15, 25, 35, 45, 55 ],
			owner => $rsync_user,
			group => $rsync_user,
      require => Account::User[$rsync_user];
	}
	
	# The contents of config.ru differ across puppet versions.
	nginx::site { puppet-production:
		config => template('puppet/server/global/puppet-production.erb'),
		content => "puppet:///modules/puppet/server/global/${puppetversion}/passenger_application",
		owner => 'puppet',
	}
	
	nrpe::check_file_age { rsync_trunk: file => '/etc/puppet.production/.revision' }

	file {
		'/etc/puppet/manifests':
			ensure => directory,
			owner => 'root',
			group => 'root',
			mode => 0755;
		'/etc/puppet/ssl':
			ensure => directory,
			owner => 'puppet',
			group => 'root',
      require => Class["puppet::accounts"],
			mode => 0771;
		'/etc/puppet/ssl/ca':
			ensure => directory,
			owner => 'puppet',
			group => 'puppet',
      require => Class["puppet::accounts"],
			mode => 0770;
		[ '/etc/puppet/ssl/ca/private', '/etc/puppet/ssl/ca/signed' ]:
			ensure => directory,
			owner => 'puppet',
			group => 'puppet',
      require => Class["puppet::accounts"],
			mode => 0770;
		'/etc/puppet/ssl/ca/requests':
			ensure => directory,
			owner => 'puppet',
			group => 'puppet',
      require => Class["puppet::accounts"],
			mode => 0755;
		[ '/etc/puppet/ssl/certificate_requests', '/etc/puppet/ssl/certs', '/etc/puppet/ssl/public_keys' ]:
			ensure => directory,
			owner => 'puppet',
			group => 'root',
      require => Class["puppet::accounts"],
			mode => 0755;
		[ '/etc/puppet/ssl/private_keys', '/etc/puppet/ssl/private' ]:
			ensure => directory,
			owner => 'puppet',
			group => 'root',
      require => Class["puppet::accounts"],
			mode => 0750;
		'/etc/puppet/ssl/ca/ca_crl.pem':
			ensure => present,
			owner => 'puppet',
			group => 'puppet',
      require => Class["puppet::accounts"],
			source => "puppet:///modules/puppet/slave/sites/${my_site}/ssl/ca/ca_crl.pem",
			mode => 0664;
		'/etc/puppet/ssl/ca/ca_crt.pem':
			ensure => present,
			owner => 'puppet',
			group => 'puppet',
      require => Class["puppet::accounts"],
			source => "puppet:///modules/puppet/slave/sites/${my_site}/ssl/ca/ca_crt.pem",
			mode => 0660;
		'/etc/puppet/ssl/ca/ca_key.pem':
			ensure => present,
			owner => 'puppet',
			group => 'puppet',
      require => Class["puppet::accounts"],
			source => "puppet:///modules/puppet/slave/sites/${my_site}/ssl/ca/ca_key.pem",
			mode => 0660;
		'/etc/puppet/ssl/ca/ca_pub.pem':
			ensure => present,
			owner => 'puppet',
			group => 'puppet',
      require => Class["puppet::accounts"],
			source => "puppet:///modules/puppet/slave/sites/${my_site}/ssl/ca/ca_pub.pem",
			mode => 0640;
		[ '/etc/puppet/ssl/ca/inventory.txt', '/etc/puppet/ssl/ca/serial' ]:
			ensure => present,
			owner => 'puppet',
			group => 'puppet',
      require => Class["puppet::accounts"],
			mode => 0644;
		'/etc/puppet/ssl/ca/private/ca.pass':
			ensure => present,
			owner => 'puppet',
			group => 'puppet',
      require => Class["puppet::accounts"],
			source => "puppet:///modules/puppet/slave/sites/${my_site}/ssl/ca/private/ca.pass",
			mode => 0660;
		'/etc/puppet/ssl/ca/signed/puppet.pem':
			ensure => present,
			owner => 'puppet',
			group => 'puppet',
      require => Class["puppet::accounts"],
			source => "puppet:///modules/puppet/slave/sites/${my_site}/ssl/ca/signed/puppet.pem",
			mode => 0640;
		'/etc/puppet/ssl/public_keys/puppet.pem':
			ensure => present,
			owner => 'puppet',
			group => 'root',
      require => Class["puppet::accounts"],
			source => "puppet:///modules/puppet/slave/sites/${my_site}/ssl/public_keys/puppet.pem",
			mode => 0644;
		'/etc/puppet/ssl/private_keys/puppet.pem':
			ensure => present,
			owner => 'puppet',
			group => 'root',
      require => Class["puppet::accounts"],
			source => "puppet:///modules/puppet/slave/sites/${my_site}/ssl/private_keys/puppet.pem",
			mode => 0600;
		'/etc/puppet/ssl/certs/puppet.pem':
			ensure => present,
			owner => 'puppet',
			group => 'root',
      require => Class["puppet::accounts"],
			source => "puppet:///modules/puppet/slave/sites/${my_site}/ssl/certs/puppet.pem",
			mode => 0644;
		'/etc/puppet/ssl/certs/ca.pem':
			ensure => present,
			owner => 'puppet',
			group => 'root',
      require => Class["puppet::accounts"],
			source => "puppet:///modules/puppet/slave/sites/${my_site}/ssl/certs/ca.pem",
			mode => 0644;
		'/etc/puppet/ssl/crl.pem':
			ensure => present,
			owner => 'puppet',
			group => 'root',
      require => Class["puppet::accounts"],
			source => "puppet:///modules/puppet/slave/sites/${my_site}/ssl/crl.pem",
			mode => 0644;
		var-log-puppet:
			path => '/var/log/puppet',
			ensure => directory,
			owner => 'puppet',
			group => 'puppet',
      require => Class["puppet::accounts"],
			mode => 0550;
		ssh-config:
			path => "${account::home}/${rsync_user}/.ssh/config",
			ensure => present,
			owner => $rsync_user,
			group => $rsync_user,
      require => Account::User[$rsync_user],
			source => 'puppet:///modules/puppet/slave/global/ssh_config',
			mode => 0644;
		ssh-private-key:
			ensure => present,
			path => "${account::home}/${rsync_user}/.ssh/id_rsa",
			owner => $rsync_user,
			group => $rsync_user,
      require => Account::User[$rsync_user],
			source => "puppet:///modules/puppet/slave/sites/${my_site}/id_rsa",
			mode => 0600;
		[ '/usr/local', '/usr/local/bin', '/usr/local/sbin' ]:
			ensure => directory,
			mode => 0755;
		puppet_slave_rsync_sh:
			ensure => present,
			path => '/usr/local/sbin/puppet_slave_rsync.sh',
			owner => $rsync_user,
      group => 'root',
      require => Account::User[$rsync_user],
			content => template('puppet/slave/global/puppet_slave_rsync.sh.erb'),
			mode => 0750;
		puppet_slave_webrick_sh:
			ensure => present,
			path => '/usr/local/sbin/puppet_slave_webrick.sh',
			group => 'puppet',
			mode => 0750,
      require => Class["puppet::accounts"],
			content => template('puppet/slave/global/puppet_slave_webrick.sh.erb');
	}

}
