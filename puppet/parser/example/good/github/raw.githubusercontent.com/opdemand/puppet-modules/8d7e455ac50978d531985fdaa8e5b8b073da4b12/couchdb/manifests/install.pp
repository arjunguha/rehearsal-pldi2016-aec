class couchdb::install {

  # use a more current couchdb version than ubuntu has
  apt::ppa {"ppa:longsleep/couchdb":}

  package {"couchdb":
    ensure => latest,
    require => Apt::Ppa["ppa:longsleep/couchdb"],
  }

  # work around couchdb package daemon issues in ubuntu 
  exec {"prevent-daemon-start":
    command => "echo '
COUCHDB_USER=couchdb
COUCHDB_STDOUT_FILE=/dev/null
COUCHDB_STDERR_FILE=/dev/null
COUCHDB_RESPAWN_TIMEOUT=5
COUCHDB_OPTIONS=
ENABLE_SERVER=0
' > /etc/default/couchdb",
    provider => shell,
  }

  exec {"allow-daemon-start":
    command => "sed -i -e s/ENABLE_SERVER=0/ENABLE_SERVER=1/ /etc/default/couchdb",
    provider => shell,
  }

  # order deps to work around packaging issue
  Exec["prevent-daemon-start"] ->
  Package["couchdb"] ->
  Exec["allow-daemon-start"]

}
