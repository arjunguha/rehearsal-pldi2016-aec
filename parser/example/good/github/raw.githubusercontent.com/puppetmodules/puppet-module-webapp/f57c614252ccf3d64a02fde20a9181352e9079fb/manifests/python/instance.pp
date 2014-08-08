define webapp::python::instance($domain,
                                $ensure=present,
                                $aliases=[],
                                $mediaroot="",
                                $mediaprefix="",
                                $wsgi_module="",
                                $django=false,
                                $django_settings="",
                                $paste=false,
                                $paste_settings="",
                                $requirements=false,
                                $workers=1,
                                $timeout_seconds=30,
                                $monit=true,
                                $monit_memory_limit=300,
                                $monit_cpu_limit=50,
                                $nginx=true,
                                $ssl=false,
                                $ssl_certificate="",
                                $ssl_certificate_key="",
                                $socket=undef,
                                $environment={},
                                $venv=undef,
                                $src=undef,
                                $requirements_path=undef) {

  if !$venv {
    $venv = "${webapp::python::venv_root}/$name"
  }

  if !$src {
    $src = "${webapp::python::src_root}/$name"
  }

  $pidfile = "${python::gunicorn::rundir}/${name}.pid"
  $real_socket = $socket ? {
    undef   => "unix:${python::gunicorn::rundir}/${name}.sock",
    default => $socket,
  }

  $owner = $webapp::python::owner
  $group = $webapp::python::group

  file { $src:
    ensure => directory,
    owner => $owner,
    group => $group,
  }

  if $nginx and $webapp::python::nginx {
    nginx::site { $name:
      ensure => $ensure,
      domain => $domain,
      aliases => $aliases,
      root => "/var/www/$name",
      mediaroot => $mediaroot,
      mediaprefix => $mediaprefix,
      upstreams => ["${real_socket}"],
      owner => $owner,
      group => $group,
      ssl => $ssl,
      ssl_certificate => $ssl_certificate,
      ssl_certificate_key => $ssl_certificate_key,
      require => Python::Gunicorn::Instance[$name],
    }
  }

  if !$requirements_path {
    $requirements_path = $requirements ? {
      true => "$src/requirements.txt",
      false => undef,
      default => "$src/$requirements",
    }
  }
  python::venv::isolate { $venv:
    ensure => $ensure,
    requirements => $requirements_path,
  }

  python::gunicorn::instance { $name:
    ensure => $ensure,
    venv => $venv,
    src => $src,
    wsgi_module => $wsgi_module,
    django => $django,
    django_settings => $django_settings,
    paste => $paste,
    paste_settings => $paste_settings,
    workers => $workers,
    timeout_seconds => $timeout_seconds,
    socket => $real_socket,
    environment => $environment,
    require => $ensure ? {
      'present' => Python::Venv::Isolate[$venv],
      default => undef,
    },
    before => $ensure ? {
      'absent' => Python::Venv::Isolate[$venv],
      default => undef,
    },
  }

  $reload = "/etc/init.d/gunicorn-$name reload"

  if $monit and $webapp::python::monit {
    $tokens = split($real_socket, ":")
    if size($tokens) > 1 and $tokens[0] == "unix" {
      $sock = $tokens[1]
    } else {
      $sock = $real_socket
    }
    monit::monitor { "gunicorn-$name":
      ensure => $ensure,
      pidfile => $pidfile,
      socket => $sock,
      checks => ["if totalmem > $monit_memory_limit MB for 2 cycles then exec \"$reload\"",
                 "if totalmem > $monit_memory_limit MB for 3 cycles then restart",
                 "if cpu > ${monit_cpu_limit}% for 2 cycles then alert"],
      require => $ensure ? {
        'present' => Python::Gunicorn::Instance[$name],
        default => undef,
      },
      before => $ensure ? {
        'absent' => Python::Gunicorn::Instance[$name],
        default => undef,
      },
    }
  }
}
