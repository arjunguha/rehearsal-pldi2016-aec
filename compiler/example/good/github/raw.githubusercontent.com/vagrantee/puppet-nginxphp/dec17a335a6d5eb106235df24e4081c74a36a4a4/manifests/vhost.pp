# = Define: nginxphp::vhost
#
define nginxphp::vhost (
    $server_name = 'vagrantee.local',
    $doc_root    = '/vagrant',
    $template    = 'nginxphp/nginx/vagrantee.erb',
    $target      = 'vagrantee',
    $nginx_dir   = '/etc/nginx'
) {

  file { "${nginx_dir}/sites-available/${target}":
    ensure  => 'present',
    content => template("${template}"),
    require => Package['nginx'],
  }

  file { "${nginx_dir}/sites-enabled/${target}":
    ensure  => 'link',
    target  => "${nginx_dir}/sites-available/${target}",
    require => [Package['nginx'], File["${nginx_dir}/sites-available/${target}"]],
    notify  => Service['nginx']
  }

}
