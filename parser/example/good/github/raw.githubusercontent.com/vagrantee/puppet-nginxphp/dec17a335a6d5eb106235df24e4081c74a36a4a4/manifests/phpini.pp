# = Define: nginxphp::phpini
#
define nginxphp::phpini (
    $value       = '',
    $template    = 'extra-ini.erb',
    $target      = 'extra.ini',
    $config_dir  = '/etc/php5/fpm'
) {

  file { "${config_dir}/conf.d/${target}":
    ensure  => 'present',
    content => template("php/${template}"),
    require => Package['php5-fpm'],
    notify  => Service['php5-fpm'],
  }

}
