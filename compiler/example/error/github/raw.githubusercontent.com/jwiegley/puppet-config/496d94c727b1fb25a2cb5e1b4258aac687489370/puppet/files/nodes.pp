# /etc/puppet/manifests/nodes.pp

node default {
  include ssh::server

  package { 'ntp':    ensure => present }

  #package { 'augeas': ensure => latest }
  #package { 'ruby-augeas':
  #  ensure   => latest,
  #  provider => gem,
  #  require  => Package[augeas] ;
  #}
}

node slave inherits default {
  include puppet::agent
}

node puppet inherits default {  # this is the puppetmaster node
  include puppet::master
}

import '/etc/puppet/site/modules/nodes.pp'

# nodes.pp ends here
