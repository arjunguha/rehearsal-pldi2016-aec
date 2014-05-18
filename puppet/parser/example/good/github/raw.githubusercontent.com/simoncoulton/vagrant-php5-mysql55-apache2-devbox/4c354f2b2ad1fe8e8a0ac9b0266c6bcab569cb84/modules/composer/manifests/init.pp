group { 'puppet': ensure => 'present' }

class composer {
  $target_dir = '/usr/local/bin'
  $tmp_dir = '/tmp'

  package { 'curl': }

  exec { 'composer_download' : 
    command => 'curl -s https://getcomposer.org/installer | php',
    cwd => $tmp_dir,
    creates => "$tmp_dir/composer.phar",
    require => [Package['curl'], Class['php54']]
  }
  
  file { "$target_dir/composer" :
    ensure => present,
    source => "$tmp_dir/composer.phar",
    require => Exec['composer_download']
  }

  exec { 'composer_update' :
    command => "$target_dir/composer self-update",
    require => File["$target_dir/composer"]
  }
}