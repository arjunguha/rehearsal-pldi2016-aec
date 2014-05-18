class lb {
  class { 'nginx': }
  nginx::resource::upstream { 'cluster_app':
        ensure  => present,
        members => [
          '33.33.33.31:8081',
          '33.33.33.32:8081'
          ],
  }
  nginx::resource::vhost { 'cluster.local':
    ensure   => present,
    proxy  => 'http://cluster_app',
  }
}
