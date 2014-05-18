class kbp_django {
  include gen_django
  include gen_base::libjs_jquery
  include kbp_apache::module::wsgi

  file { "/srv/django":
    ensure => directory;
  }

  # Fix for Debian bug #720921, might be needed for Squeeze as well
  if $lsbdistcodename == 'wheezy' {
    file {
      '/usr/share/pyshared/django/contrib/admin/static/admin/js/jquery.js':
        ensure  => link,
        target  => '/usr/share/javascript/jquery/jquery.js',
        require => Package['python-django'];
      '/usr/share/pyshared/django/contrib/admin/static/admin/js/jquery.min.js':
        ensure  => link,
        target  => '/usr/share/javascript/jquery/jquery.min.js',
        require => Package['python-django'];
    }
  }
}

define kbp_django::site($settings='settings', $root_path='/', $root_django="/${name}", $static_path='/media', $static_django="/${name}/media", $auth=false, $cert=false, $wildcard=false, $address6='::',
    $intermediate=false, $monitor=true, $make_default=false, $serveralias=false, $monitor_path=false, $address='*', $monitor_ip=false, $monitor_statuscode=false, $monitor_proxy=false, $wsgi_file='dispatch.wsgi',
    $wsgi_owner='root', $run_daily_cleanup=false, $run_daily_cleanup_dev=false, $documentroot = "/srv/www/${name}", $wsgi_daemon_mode=false, $access_logformat='vhostcombined', $full_wsgi_path=false, $wsgi_user='www-data',
    $wsgi_group='www-data') {
  include kbp_django

  kbp_apache::site { $name:
    address            => $address,
    auth               => $auth,
    documentroot       => $documentroot,
    wildcard           => $wildcard,
    cert               => $cert,
    intermediate       => $intermediate,
    monitor            => $monitor,
    make_default       => $make_default,
    serveralias        => $serveralias,
    monitor_proxy      => $monitor_proxy,
    monitor_path       => $monitor_path,
    monitor_ip         => $monitor_ip,
    monitor_statuscode => $monitor_statuscode,
    access_logformat   => $access_logformat;
  }

  if $wildcard or $intermediate or $cert {
    $real_ssl = true
  }

  kbp_django::app { $name:
    vhost            => $name,
    port             => $real_ssl ? {
      true    => 443,
      default => 80,
    },
    settings         => $settings,
    root_path        => $root_path,
    root_django      => $root_django,
    static_path      => $static_path,
    static_django    => $static_django,
    wsgi_file        => $wsgi_file,
    wsgi_owner       => $wsgi_owner,
    wsgi_daemon_mode => $wsgi_daemon_mode,
    wsgi_user        => $wsgi_user,
    wsgi_group       => $wsgi_group,
    full_wsgi_path   => $full_wsgi_path;
  }

  if $run_daily_cleanup {
    $cleaned_name = regsubst($name, '[._ ]', '-', 'G')

    file { "/etc/cron.daily/django-sessions-cleanup-for-${cleaned_name}":
      content => template('kbp_django/daily-cleanup.cron'),
      mode    => 755,
    }
  }
}

define kbp_django::app($vhost, $port, $settings='settings', $root_path='/', $root_django="/${name}", $static_path='/media', $static_django="/${name}/media", $vhost_addition_prefix='', $wsgi_file='dispatch.wsgi',
    $wsgi_owner='root', $wsgi_daemon_mode=false, $wsgi_process_name=false, $wsgi_processes=1, $wsgi_threads=15, $wsgi_user='www-data', $wsgi_group='www-data', $wsgi_umask='0002', $wsgi_maximum_requests=0,
    $wsgi_display_name=false, $full_wsgi_path=false) {
  include kbp_django

  if ! $wsgi_process_name {
    $real_wsgi_process_name = $name
  } else {
    $real_wsgi_process_name = $wsgi_process_name
  }

  if ! $wsgi_display_name {
    $real_wsgi_display_name = "WSGI ${real_wsgi_process_name}"
  } else {
    $real_wsgi_display_name = $wsgi_display_name
  }

  kbp_apache::vhost_addition { "${vhost}/${vhost_addition_prefix}django":
    ports   => $port,
    content => template("kbp_django/vhost-additions/django");
  }

  if !defined(File["/srv/django${root_django}"]) {
    file { "/srv/django${root_django}":
      ensure => directory,
      mode   => 775;
    }
  }

  if $wsgi_file == 'dispatch.wsgi' and !defined(File["/srv/django${root_django}/dispatch.wsgi"]) {
    file { "/srv/django${root_django}/dispatch.wsgi":
      content => template("kbp_django/dispatch.wsgi"),
      owner   => $wsgi_owner,
      replace => false,
      mode    => 775;
    }
  }

  if ! defined(File["/srv/django${static_django}"]) {
    file { "/srv/django${static_django}":
      ensure => directory,
      mode   => 775;
    }
  }
}
