define ezpublish::install::fetch::git ($www, $ezpublish_folder) {
  file { "$www/preparezpublish.sh":
    ensure => file,
    content => template('ezpublish/preparezpublish.sh.erb'),
    owner   => 'apache',
    group   => 'apache',
    mode    => '770',
  } ~>
  exec { "prepare eZ Publish":
    command => "$www/preparezpublish.sh $www $ezpublish_folder",
    path    => "/usr/local/bin/:/bin/",
    timeout => 0,
    returns => [ 0, 255 ]
  }
}