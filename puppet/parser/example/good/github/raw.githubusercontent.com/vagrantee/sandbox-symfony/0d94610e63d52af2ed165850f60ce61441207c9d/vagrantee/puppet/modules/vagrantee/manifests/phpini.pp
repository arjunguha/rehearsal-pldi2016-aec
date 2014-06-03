# = Define: vagrantee::phpini
# Based on the example42 php module, customised here to match the paths on apache 2.4.6
#
define vagrantee::phpini (
    $value       = '',
    $template    = 'extra-ini.erb',
    $target      = 'extra.ini',
    $service     = 'apache',
    $config_dir  = '/etc/php5'
) {

  file { "${config_dir}/apache2/conf.d/${target}":
    ensure  => 'present',
    content => template("php/${template}"),
    require => Package['php'],
    notify  => Service[$service],
  }

  file { "${config_dir}/cli/conf.d/${target}":
    ensure  => 'present',
    content => template("php/${template}"),
    require => Package['php'],
  }

}
