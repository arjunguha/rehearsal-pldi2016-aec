class couchdb::service {

  service {"couchdb":
    enable    => true,
    ensure    => running,
    hasstatus => true,
    require   => [Class[Couchdb::Install], Class[Couchdb::Config]],
    subscribe => File["/etc/couchdb/local.ini"],
  }

}
