# Author: Kumina bv <support@kumina.nl>

class kbp_physical::bonding {
  include gen_base::ifenslave-2_6
  include kbp_icinga::bonding

  file { "/etc/modprobe.d/bonding":
    ensure => absent;
  }
}

# Class: kbp_physical
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_physical {
  if ! $dont_install_virtualization {
    kbp_libvirt { "kbp_libvirt":; }
    include kbp_kvm
    include gen_base::bridge-utils
    include gen_base::vlan
  }

  if $raidcontroller0_driver {
    case $raidcontroller0_driver {
      "3w-9xxx": {
        $package = '3ware-cli-binary'
        $driver  = '3ware'
      }
      "aacraid": {
        $package = 'arcconf'
        $driver  = 'adaptec'
      }
      'megaraid_sas': {
        $package = 'megacli'
        $driver  = 'megaraid_sas'
      }
      'mptsas': {
        $package = ['lsiutil','python-pexpect']
        $driver  = 'lsimpt'
      }
    }

    package { $package:; }

    kbp_icinga::raidcontroller { 'controller0':
      driver => $driver;
    }
  }

  if $consolefqdn != -1 {
    if ! $consolefqdn {
      fail("\$consolefqdn has not been set in the site.pp")
    }
    if ! $consoleaddress {
      fail("\$consoleaddress has not been set in the site.pp")
    }

    if !$consoleipmi {
      if ! $consolessl and ! $consolepath and ! $consolestatus {
        kbp_icinga::virtualhost { $consolefqdn:
          address              => $consoleaddress,
          parents              => $consoleparent,
          proxy                => $consoleproxy,
          preventproxyoverride => true;
        }

        kbp_icinga::http { "http_${consolefqdn}":
          customfqdn           => $consolefqdn,
          proxy                => $consoleproxy,
          preventproxyoverride => true;
        }
      } else {
        kbp_icinga::site { "${consolefqdn}_${consoleaddress}":
          proxy                => $consoleproxy,
          ssl                  => $consolessl,
          path                 => $consolepath,
          statuscode           => $consolestatus,
          vhost                => false,
          preventproxyoverride => true;
        }
      }
    } else {
      kbp_icinga::virtualhost { $consolefqdn:
        address              => $consoleaddress,
        parents              => $consoleparent,
        proxy                => $consoleproxy,
        preventproxyoverride => true;
      }
    }
  }

  # Backup the MBR
  file { "/etc/backup/prepare.d/mbr":
    content => template("kbp_physical/mbr"),
    mode    => 700,
    require => Package["backup-scripts"];
  }

  # Install some firmware packages, maybe not all are needed, but no loss in having them installed
  package { ['firmware-bnx2','firmware-ralink','bluez-firmware','zd1211-firmware','libertas-firmware','firmware-linux-nonfree','firmware-qlogic','firmware-netxen','firmware-iwlwifi',
             'firmware-intelwimax','firmware-bnx2x','atmel-firmware','firmware-atheros']:
    ensure => latest,
  }

  # And make sure they have the correct permissions
  file { "/lib/firmware":
    owner   => 'root',
    group   => 'root',
    recurse => true,
  }
}
