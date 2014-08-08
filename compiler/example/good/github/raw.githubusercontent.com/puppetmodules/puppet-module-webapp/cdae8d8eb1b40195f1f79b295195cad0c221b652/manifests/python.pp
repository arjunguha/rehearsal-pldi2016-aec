class webapp::python($ensure=present,
                     $owner="www-data",
                     $group="www-data",
                     $src_root="/usr/local/src",
                     $venv_root="/usr/local/venv",
                     $nginx=true,
                     $nginx_workers=1,
                     $monit=true,
                     $monit_admin="",
                     $monit_interval=60) {

  if $nginx {
    class { "nginx":
      ensure => $ensure,
      workers => $nginx_workers
    }
  }

  class { "python::dev":
    ensure => $ensure,
  }

  class { "python::venv":
    ensure => $ensure,
    owner => $owner,
    group => $group
  }

  class { "python::gunicorn":
    ensure => $ensure,
    owner => $owner,
    group => $group
  }

  if $monit {
    class { monit:
      ensure => $ensure,
      admin => $monit_admin,
      interval => $monit_interval
    }
  }

}

