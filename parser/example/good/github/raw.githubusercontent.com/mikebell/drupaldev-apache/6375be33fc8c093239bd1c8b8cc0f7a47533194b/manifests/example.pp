# Define your sites here
$sites = [
    'example',
]

# Magic
define mySites {
  apache::vhost { "${name}.drupal.dev":
    server_name   => "${name}.drupal.dev",
    serveraliases => [
    ],
    docroot       => "/var/www/${name}.drupal.dev",
    port          => '80',
    env_variables => [
    ],
    priority      => '1',
  }

  mysql::db { $name:
    user     => $name,
    password => $name,
    host     => 'localhost',
    grant    => ['all'],
  }

  file { "/var/www/${name}.drupal.dev":
    ensure => "directory",
  }
}

mySites { $sites: }
