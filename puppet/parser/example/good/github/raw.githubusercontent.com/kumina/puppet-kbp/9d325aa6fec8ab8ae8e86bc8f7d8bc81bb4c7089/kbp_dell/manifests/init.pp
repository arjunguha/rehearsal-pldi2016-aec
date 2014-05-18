# Author: Kumina bv <support@kumina.nl>

# Class: kbp_dell::poweredge
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_dell::poweredge {
  include ipmi

  define line($file, $line, $ensure = 'present') {
    case $ensure {
      default: {
        err("unknown ensure value ${ensure}")
      }
      present: {
        exec { "/bin/echo '${line}' >> '${file}'":
          unless => "/bin/grep -Fx '${line}' '${file}'"
        }
      }
      absent: {
        exec { "/usr/bin/perl -ni -e 'print unless /^\\Q${line}\\E\$/' '${file}'":
          onlyif => "/bin/grep -Fx '${line}' '${file}'"
        }
      }
    }
  }

  gen_munin::client::plugin {
    # Graph the IPMI sensors for temperature
    "ipmi_sensor_u_degrees_c":
      ensure => present;
    # SMART is not supported on the Dell drives
    "hddtemp_smartctl":
      ensure => absent;
  }

  gen_munin::client::plugin::config { "ipmi_sensor_":
    section => "ipmi_sensor_*",
    content => "user root",
  }

  line { "module-e752x_edac":
    file => "/etc/modules",
    line => "e752x_edac"
  }
}

# Class: kbp_dell::pe1955
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_dell::pe1955 inherits kbp_dell::poweredge {
  # RAID controller utility
  package { "mpt-status":
    ensure => installed,
  }

  service { "mpt-statusd":
    ensure => running,
    require => Package["mpt-status"]
  }

  line { "module-mptctl":
    file => "/etc/modules",
    line => "mptctl",
  }
}

# Class: kbp_dell::pe1950
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_dell::pe1950 inherits kbp_dell::poweredge {
  include kbp_dell::perc

  gen_munin::client::plugin { "ipmi_sensor_u_rpm":
    script_path => "/usr/local/share/munin/plugins",
    script => "ipmi_sensor_",
  }
}

# Class: kbp_dell::pe2950
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_dell::pe2950 inherits kbp_dell::poweredge {
  include kbp_dell::perc

  gen_munin::client::plugin { "ipmi_sensor_u_rpm":
    script_path => "/usr/local/share/munin/plugins",
    script => "ipmi_sensor_",
  }
}

# Class: kbp_dell::perc
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_dell::perc {
  package { "megacli":
    ensure => installed,
  }
}
