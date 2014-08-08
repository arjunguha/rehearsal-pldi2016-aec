# Author: Kumina bv <support@kumina.nl>

# Class: kbp_puppet
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_puppet {
  include gen_puppet

  # We backport the squeeze-backports versions to lenny-kumina
  # The default wheezy packages are new enough
  gen_apt::preference { ["puppet","puppet-common","facter"]:
    repo   => $lsbdistcodename ? {
      "lenny"           => "lenny-kumina",
      "squeeze"         => "squeeze-backports",
      default           => $lsbdistcodename,
    },
    ensure => $lsbdistcodename ? {
      /(lenny|squeeze)/ => present,
      default           => absent,
    };
  }

  # Pin augeas to lenny-backports for lenny
  if $lsbdistcodename == "lenny" {
    gen_apt::preference { ["libaugeas-ruby", "libaugeas-ruby1.8", "augeas-lenses", "libaugeas0", "augeas-tools"]:;}
  }

  Kbp_puppet::Settestpms <<| |>>

  # Create a facts.yaml for easier getting of those facts.
  file { "/etc/puppet/facts.yaml":
    content => template("kbp_puppet/facts"),
    require => Package["puppet-common"];
  }
}

# Class: kbp_puppet::test_default_config
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_puppet::default_config {
  include gen_puppet::puppet_conf

  # Default config for all our puppet clients
  gen_puppet::set_config {
    "logdir":      value => '/var/log/puppet';
    "vardir":      value => '/var/lib/puppet';
    "ssldir":      value => '/var/lib/puppet/ssl';
    "rundir":      value => '/var/run/puppet';
    # Single quotes in the next resources prevent them being expanded
    "factpath":    value => '$vardir/lib/facter';
    "templatedir": value => '$confdir/templates';
    "pluginsync":  value => 'true';
    "environment": value => $environment;
    "configtimeout":
      value   => '1800',
      section => 'agent';
    "splay":
      value   => 'false',
      section => "agent";
    "server":
      value   => 'puppet1.kumina.nl',
      section => "agent";
    "report":
      value   => 'false',
      section => "agent";
  }

  # We're trying to create the numbers so we only need to set one to change the runinterval.
  # We limit ourselves to only allow full hour intervals.
  $runinterval_in_hours = 5

  # Don't change these values
  $hours = inline_template("<%= (0..23).step(runinterval_in_hours.to_i).to_a.join(',') %>")
  $sleep = fqdn_rand($runinterval_in_hours*3600)

  kcron { "run-puppet":
    mailto  => "reports@kumina.nl",
    command => "/bin/sleep ${sleep}; /usr/bin/test ! -f /etc/puppet/dontrunpuppetd && /usr/bin/puppet agent --enable && /usr/bin/nice /usr/bin/ionice -c 3 /usr/bin/puppet agent --onetime --no-daemonize --no-splay --color false --logdest console --logdest syslog >/dev/null 2>&1",
    hour    => $hours,
    minute  => "0",
  }

  # Make sure we're not starting puppet at a reboot
  exec { "Disable puppet on boot":
    command => "/bin/sed -i 's/START=.*$/START=no/' /etc/default/puppet && /etc/init.d/puppet stop",
    onlyif  => "/bin/grep -q 'START=yes' /etc/default/puppet",
    require => Package["puppet"],
  }
}

# Class: kbp_puppet::vim
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_puppet::vim {
  include kbp_vim::puppet
}

define kbp_puppet::settestpms($testpms) {
  Concat <| |> {
    testpms => $testpms,
  }
}
