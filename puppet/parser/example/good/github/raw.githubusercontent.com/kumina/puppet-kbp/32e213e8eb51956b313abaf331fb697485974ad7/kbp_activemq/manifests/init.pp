# Author: Kumina bv <support@kumina.nl>

# Class: kbp_activemq
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_activemq {
  include gen_activemq
  include kbp_ferm
  include kbp_trending::activemq
  include kbp_icinga::activemq
  include kbp_collectd::plugin::activemq

  if $lsbdistcodename == 'squeeze' {
    file {
      "/etc/activemq/activemq.xml":
        content => template("kbp_activemq/activemq.xml"),
        notify  => Exec["/bin/rm -Rf /var/lib/activemq/*"],
        require => Package["activemq"];
      "/etc/activemq/jetty.xml":
        content => template("kbp_activemq/jetty.xml"),
        notify  => Exec["reload-activemq"],
        require => Package["activemq"];
    }
  }

  if $lsbdistcodename == 'wheezy' {
    file {
      "/etc/activemq/instances-enabled/main":
        ensure  => directory,
        require => Package["activemq"];
      "/etc/activemq/instances-enabled/main/activemq.xml":
        content => template("kbp_activemq/activemq.xml"),
        notify  => Exec["/bin/rm -Rf /var/lib/activemq/*"],
        require => Package["activemq"];
      "/etc/activemq/instances-enabled/main/jetty.xml":
        content => template("kbp_activemq/jetty.xml"),
        notify  => Exec["reload-activemq"],
        require => Package["activemq"];
    }
  }

  exec { "/bin/rm -Rf /var/lib/activemq/*":
    refreshonly => true,
    notify      => Service["activemq"],
  }

  # Open the management port
  gen_ferm::rule { "Connections to admin port":
    dport  => "8161",
    proto  => "tcp",
    saddr  => "${fqdn}",
    action => "ACCEPT",
  }
}
