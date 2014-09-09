# Author: Kumina bv <support@kumina.nl>

# Class: kbp_cassandra::client
#
# Parameters:
#  customtag
#    Undocumented
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_cassandra::client($customtag="cassandra_${environment}",$ferm_saddr=$external_ipaddress) {
  kbp_ferm::rule { "Cassandra connections from ${fqdn}":
    exported => true,
    saddr    => $ferm_saddr,
    proto    => "tcp",
    dport    => 9160,
    action   => "ACCEPT",
    ferm_tag => $customtag;
  }
}

# Class: kbp_cassandra::server
#
# Parameters:
#  java_monitoring
#    Undocumented
#  servicegroups
#    Undocumented
#  sms
#    Undocumented
#  customtag
#    Undocumented
#
# Actions:
#  Undocumented
#
# Depends:
#  kbp_icinga::cassandra
#  gen_cassandra
#  gen_puppet
#
class kbp_cassandra::server($branch="07x", $customtag="cassandra_${environment}", $java_monitoring=false, $servicegroups=false, $sms=true, $use_ipaddress=$external_ipaddress, $jmx_port=7199) {
  include kbp_icinga::cassandra
  class { "gen_cassandra":
    branch => $branch;
  }

  # Make sure we use the Sun Java package
  Package <| title == "cassandra" |> {
    require => Package["sun-java6-jdk"],
  }

  kbp_ferm::rule { "Internal Cassandra connections from ${fqdn}":
    exported => true,
    saddr    => $use_ipaddress,
    proto    => "tcp",
    dport    => 7000,
    action   => "ACCEPT",
    ferm_tag => $customtag;
  }

  Kbp_ferm::Rule <<| tag == $customtag |>>
  Gen_ferm::Rule <<| tag == "cassandra_monitoring" |>>

  if $java_monitoring {
    kbp_icinga::java { "cassandra_${jmx_port}":
      servicegroups  => $servicegroups ? {
        false   => undef,
        default => $servicegroups,
      },
      sms            => $sms;
    }
  }

  # This cronjob creates a daily snapshot.
  kcron { "cassandra-0":
    command => "/usr/bin/nodetool -h ${hostname} -p ${jmx_port} snapshot -t backup > /dev/null; /bin/rm -rf /var/backups/cassandra && /bin/mkdir /var/backups/cassandra && for i in `ls /var/lib/cassandra/data/`; do mkdir /var/backups/cassandra/\$i; for j in `ls /var/lib/cassandra/data/\$i/`; do mkdir /var/backups/cassandra/\$i/\$j; if [ -d /var/lib/cassandra/data/\$i/\$j/snapshots/backup ]; then mv /var/lib/cassandra/data/\$i/\$j/snapshots/backup /var/backups/cassandra/\$i/\$j; fi; done; done",
    require => Package['cassandra'],
    hour    => '18',
    minute  => '0',
  }

  # Don't backup the data directory.
  kbp_backup::exclude { "/var/lib/cassandra/":; }
}
