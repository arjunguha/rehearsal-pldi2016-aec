# Class: nginx
#
# This module installs Nginx and its default configuration using rvm as the provider.
#
# Parameters:
#   $ruby_version
#       Ruby version to install.
#   $passenger_version
#      Passenger version to install.
#   $logdir
#      Nginx's log directory.
#   $installdir
#      Nginx's install directory.
#   $www
#      Base directory for
# Actions:
#
# Requires:
#    puppet-rvm
#
# Sample Usage:  include nginx
class nginx (
  $ruby_version = 'ruby-1.9.3-p125',
  $passenger_version = '3.0.12',
  $logdir = '/var/log/nginx',
  $installdir = '/opt/nginx',
  $www    = '/var/www' ) {

    $options = "--auto --auto-download  --prefix=${installdir}"
    $passenger_deps = [ 'libcurl4-openssl-dev' ]

    include rvm

    package { $passenger_deps: ensure => present }

    rvm_system_ruby {
      $ruby_version:
        ensure      => 'present',
        default_use => true;
    }

    rvm_gem {
      "${ruby_version}/passenger":
        ensure => $passenger_version,
    }

    exec { 'create container':
      command => "/bin/mkdir ${www} && /bin/chown www-data:www-data ${www}",
      unless  => "/usr/bin/test -d ${www}",
      before  => Exec['nginx-install']
    }

    exec { 'nginx-install':
      command => "/bin/bash -l -i -c \"/usr/local/rvm/gems/${ruby_version}/bin/passenger-install-nginx-module ${options}\"",
      group   => 'root',
      unless  => "/usr/bin/test -d ${installdir}",
      require => [ Package[$dependencies_passenger], Rvm_system_ruby[$ruby_version], Rvm_gem["${ruby_version}/passenger"]];
    }

    file { 'nginx-config':
      path    => "${installdir}/conf/nginx.conf",
      owner   => 'root',
      group   => 'root',
      mode    => '0644',
      content => template('nginx/nginx.conf.erb'),
      require => Exec['nginx-install'],
    }

    exec { 'create sites-conf':
      path    => ['/usr/bin','/bin'],
      unless  => "/usr/bin/test -d  ${installdir}/conf/sites-available && /usr/bin/test -d ${installdir}/conf/sites-enabled",
      command => "/bin/mkdir  ${installdir}/conf/sites-available && /bin/mkdir ${installdir}/conf/sites-enabled",
      require => Exec['nginx-install'],
    }

    file { 'nginx-service':
      path      => '/etc/init.d/nginx',
      owner     => 'root',
      group     => 'root',
      mode      => '0755',
      content   => template('nginx/nginx.init.erb'),
      require   => File['nginx-config'],
      subscribe => File['nginx-config'],
    }

    file { $logdir:
      ensure => directory,
      owner  => 'root',
      group  => 'root',
      mode   => '0644'
    }

    service { 'nginx':
      ensure     => running,
      enable     => true,
      hasrestart => true,
      hasstatus  => true,
      subscribe  => File['nginx-config'],
      require    => [ File[$logdir], File['nginx-service']],
    }

}
