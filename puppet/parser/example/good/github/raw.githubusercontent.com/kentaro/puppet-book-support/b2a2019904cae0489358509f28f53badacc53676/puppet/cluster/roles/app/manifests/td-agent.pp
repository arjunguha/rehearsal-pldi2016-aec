class app::td-agent {
  include ::td-agent
  include app::td-agent::config

     Class['::td-agent::install']
  -> Class['app::td-agent::config']
  ~> Class['::td-agent::service']
}
