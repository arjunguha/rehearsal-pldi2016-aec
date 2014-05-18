class kbp_dashboard_new::site_host($url, $prod_url, $ssl=true, $dbpassword) {
  include gen_base::python_django_south
  include gen_base::python-ipaddr
  include gen_base::memcached
  include gen_base::python_memcache
  include gen_base::python_django_debug_toolbar
  include gen_base::python_psycopg2
  include gen_base::python_mysqldb
  include gen_base::python_zmq
  include gen_base::zmq
  include gen_base::python_daemon

  gen_apt::preference { 'python-zmq':; }

  $port = $ssl ? {
    false => 80,
    true  => 443,
  }

  kbp_mysql::client { 'dashboard_new':; }

  @@mysql::server::grant { "dashboard_new on puppet for ${fqdn}":
    user        => 'dashboard_new',
    db          => 'puppet',
    hostname    => $fqdn,
    password    => $dbpassword,
    permissions => 'SELECT',
    tag         => "mysql_${environment}_${custenv}";
  }

  Kbp_dashboard_new::Environment <<| |>> {
    url      => $url,
    prod_url => $prod_url,
    port     => $port,
  }
}

define kbp_dashboard_new::environment($url, $prod_url, $port, $prettyname) {
  kbp_apache::vhost_addition { "${url}/proxies_${name}":
    ports   => $port,
    content => template('kbp_dashboard_new/vhost-additions/proxies');
  }
}
