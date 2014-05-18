# Author: Kumina bv <support@kumina.nl>

# Class: kbp_hetzner
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_hetzner inherits hetzner {
  gen_ferm::rule {
    "Allow guests to connect to the internet":
      chain     => "FORWARD",
      interface => "ubr1",
      outerface => "ubr0",
      action    => "ACCEPT";
    "Allow the internet to connect to guests":
      chain     => "FORWARD",
      interface => "ubr0",
      outerface => "ubr1",
      action    => "ACCEPT";
  }
}

# Class: kbp_hetzner::sensors
#
# Actions:
#  Configure sensors on Hetzner hosts
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_hetzner::sensors {
  package { "lm-sensors":
    ensure => "latest";
  }

  gen_munin::client::plugin { "sensors_temp":
    require => Package["lm-sensors"],
    script  => "sensors_",
    notify  => Exec["/sbin/modprobe f71882fg"];
  }

  exec { "/sbin/modprobe f71882fg":
    refreshonly => true;
  }

  line { "f71882fg": # Load the module on boot
    file    => "/etc/modules",
    ensure  => "present",
    content => "f71882fg";
  }
}
