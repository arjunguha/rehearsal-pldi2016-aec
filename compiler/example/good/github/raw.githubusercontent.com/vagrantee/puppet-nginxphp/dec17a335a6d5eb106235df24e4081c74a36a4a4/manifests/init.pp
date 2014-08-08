# = Class: nginxphp
#
# Main nginxphp manifest
#

class nginxphp() {

  package { ['nginx', 'php5-fpm']:
    ensure  => 'installed'
  }

  service { 'nginx':
    ensure     => running,
    enable     => true,
  }

  service { 'php5-fpm':
    ensure     => running,
    enable     => true,
  }
}