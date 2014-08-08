class kbp_dashboard::site_host($url, $ssl=true, $dbpassword, $pdbhost, $idbhost=$pdbhost) {
  include gen_base::python_django_south
  include gen_base::python_mysqldb
  include gen_base::python_psycopg2
  include gen_base::python-ipaddr
  include gen_base::python_memcache
  include gen_base::python_psycopg2
  include gen_base::python_zmq
  include gen_base::python_django_oauth_plus
  include gen_base::python_oauth2
  include gen_base::zmq

  gen_apt::preference {
    'python-zmq':;
    'python-django-oauth-plus':
      repo => 'wheezy-kumina';
  }

  $port = $ssl ? {
    false => 80,
    true  => 443,
  }

  Kbp_dashboard::Environment <<| |>> {
    url         => $url,
    port        => $port,
  }

  kbp_mysql::client { 'dashboard':; }

  @@mysql::server::grant { "dashboard on puppet for ${fqdn}":
    user        => 'dashboard',
    db          => 'puppet',
    hostname    => $fqdn,
    password    => $dbpassword,
    permissions => 'SELECT',
    tag         => "mysql_${environment}_${custenv}";
  }

  file { '/srv/django/dashboard.kumina.nl/dashboard/fill':
    content => "/srv/django/dashboard.kumina.nl/dashboard/fill_dashboard_database -ps ${pdbhost} -pd puppet -pp ${dbpassword} -is ${idbhost} -id icinga -ip ${dbpassword}",
    mode    => 755;
  }

  kcron { 'filldashboarddb':
    command => "/srv/django/dashboard.kumina.nl/dashboard/fill >/dev/null",
    minute  => '0,30';
  }
}

define kbp_dashboard::environment($url, $port, $prettyname) {
  kbp_apache::vhost_addition { "${url}/proxies_${name}":
    ports   => $port,
    content => template('kbp_dashboard/vhost-additions/proxies');
  }
}
