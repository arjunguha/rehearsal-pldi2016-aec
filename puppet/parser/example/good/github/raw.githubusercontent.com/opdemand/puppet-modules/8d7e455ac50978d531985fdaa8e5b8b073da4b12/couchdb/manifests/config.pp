class couchdb::config {

  require couchdb::params

  file {"/etc/couchdb/local.ini":
    content => template("couchdb/local.ini.erb"),
    require => Class[Couchdb::Install],
  }

  # Overwrite init.d script to respect ENABLE_SERVER flag
  file {"/etc/init.d/couchdb":
    content => template("couchdb/couchdb.erb"),
    mode    => 0755,
  }

}
