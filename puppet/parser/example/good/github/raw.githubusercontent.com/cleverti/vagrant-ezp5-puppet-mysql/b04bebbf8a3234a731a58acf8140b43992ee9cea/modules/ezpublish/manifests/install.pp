class ezpublish::install {
  ezpublish::install::fetch{ 'fetch':
    www              => $www, 
    ezpublish_src    => $ezpublish_src, 
    ezpublish_folder => $ezpublish_folder, 
    ezpublish        => $ezpublish, 
    type             => $type
  } ~>
  exec { "setfacl-R":
    command => "/usr/bin/setfacl -R -m u:apache:rwx -m u:apache:rwx $www/$ezpublish_folder/ezpublish/{cache,logs,config} $www/$ezpublish_folder/ezpublish_legacy/{design,extension,settings,var} web",
    onlyif  => '/usr/bin/test -d $www/$ezpublish_folder',
    returns => [ 1 ]
  } ~>
  exec { "setfacl-dR":
    command => "/usr/bin/setfacl -dR -m u:apache:rwx -m u:vagrant:rwx $www/$ezpublish_folder/ezpublish/{cache,logs,config} $www/$ezpublish_folder/ezpublish_legacy/{design,extension,settings,var} web",
    onlyif  => '/usr/bin/test -d $www/$ezpublish_folder',
    returns => [ 0, 1, 2, '', ' ']
  } ~>
  exec { "remove_cache":
    command => "/bin/rm -rf $www/$ezpublish_folder/ezpublish/cache/*",
    onlyif  => '/usr/bin/test -d $www/$ezpublish_folder'
  } ~>
  file { "$www/$ezpublish_folder/ezpublish_legacy/kickstart.ini":
    ensure => file,
    content => template('ezpublish/kickstart.ini.erb'),
    owner   => 'apache',
    group   => 'apache',
    mode    => '666',
  } ~>
  exec { "assets_install":
    command => "/usr/bin/php $www/$ezpublish_folder/ezpublish/console assets:install --symlink $www/$ezpublish_folder/web",
    onlyif  => ['/usr/bin/test -d $www/$ezpublish_folder','/usr/bin/test -d $www/$ezpublish_folder/vendor'],
  } ~>
  exec { "legacy_assets":
    command => "/usr/bin/php $www/$ezpublish_folder/ezpublish/console ezpublish:legacy:assets_install --symlink $www/$ezpublish_folder/web",
    onlyif  => ['/usr/bin/test -d $www/$ezpublish_folder','/usr/bin/test -d $www/$ezpublish_folder/vendor'],
  } ~>
  exec { "assetic_dump":
    command => "/usr/bin/php $www/$ezpublish_folder/ezpublish/console assetic:dump",
    onlyif  => ['/usr/bin/test -d $www/$ezpublish_folder','/usr/bin/test -d $www/$ezpublish_folder/vendor'],
  } ~>
  file { "$www/$ezpublish_folder/install_packages.sh":
    ensure => file,
    content => template('ezpublish/install_packages.sh.erb'),
    owner   => 'apache',
    group   => 'apache',
    mode    => '770',
  } ~>
  exec { "fetch_packages":
    command => "/bin/bash $www/$ezpublish_folder/install_packages.sh",
    path    => "/usr/local/bin/:/bin/",
    returns => [ 0, 1 ]
  }
}