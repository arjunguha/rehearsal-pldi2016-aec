# Author: Kumina bv <support@kumina.nl>

# Class: kbp_ssh
#
# Actions:
#  Setup ssh the way we want it
#
# Depends:
#  kbp_openssl::common
#  gen_ferm::rule
#  gen_puppet
#
class kbp_ssh {
  include kbp_openssl::common

  gen_ferm::rule { "SSH":
    proto  => "tcp",
    dport  => "22",
    action => "ACCEPT",
    tag    => "ferm";
  }

  @@sshkey { $fqdn:
    host_aliases => $ipaddress,
    type         => ssh-rsa,
    key          => $sshrsakey,
    tag          => "sshkey_${environment}",
    ensure       => present;
  }

  Sshkey <<| tag == "sshkey_${environment}" |>>

  # Disable password logins and root logins
  kaugeas {
    "sshd_config PermitRootLogin":
      lens    => 'Sshd.lns',
      file    => "/etc/ssh/sshd_config",
      changes => "set PermitRootLogin no",
      notify  => Service["ssh"];
    "sshd_config PasswordAuthentication":
      lens    => 'Sshd.lns',
      file    => "/etc/ssh/sshd_config",
      changes => "set PasswordAuthentication no",
      notify  => Service["ssh"];
  }

  # Enable ClientAliveInterval messages
  kaugeas { "sshd_config ClientAliveInterval":
    lens    => 'Sshd.lns',
    file    => "/etc/ssh/sshd_config",
    changes => "set ClientAliveInterval 60",
    notify  => Service["ssh"];
   }

  if $lsbdistcodename != 'lenny' {
    kaugeas { "sshd_config DebianBanner":
      lens    => 'Sshd.lns',
      file    => "/etc/ssh/sshd_config",
      changes => "set DebianBanner no",
      notify  => Service["ssh"];
    }
  }

  # Fix permissions.
  file {
    "/etc/ssh/ssh_known_hosts":;
    '/root/.ssh':
      ensure => directory,
      mode   => 700;
  }
}

# Class: kbp_ssh::permit_root_logins_with_forced_commands
#
# Actions:
#  Allow root logins with forced commands only
#
# Depends:
#  kbp_ssh
#  gen_puppet
#
class kbp_ssh::permit_root_logins_with_forced_commands {
  Kaugeas <| title == "sshd_config PermitRootLogin" |> {
    changes => "set PermitRootLogin forced-commands-only",
  }
}

# Define: kbp_ssh::sshd_config
#
# Actions:
#  Allow groups to sftp with no other privileges
#
# Depends:
#  kbp_ssh
#  gen_puppet
#
define kbp_ssh::sftp_only () {
  kaugeas {
    'sshd_config subsystem add internal sftp':
      lens    => 'Sshd.lns',
      file    => "/etc/ssh/sshd_config",
      changes => "set Subsystem/sftp internal-sftp",
      notify  => Service["ssh"];
    "sshd_config User ${name} can only sftp":
      lens    => 'Sshd.lns',
      file    => "/etc/ssh/sshd_config",
      changes => ["set Match[1]/Condition/User '${name}'",
                  "set Match[1]/Settings/X11Forwarding 'no'",
                  "set Match[1]/Settings/ForceCommand 'internal-sftp'",
                  "set Match[1]/Settings/AllowTCPForwarding 'no'"],
      notify  => Service["ssh"];
  }
}

