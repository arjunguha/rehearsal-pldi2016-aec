class stash::ssl {
  require stash::params

  file { "${stash::params::webappdir}/conf/server.xml":
    content => template('stash/server-ssl.xml.erb'),
    mode    => '0644',
    require => Class['stash::install'],
  }
}