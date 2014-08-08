class ssh::server inherits ssh
{
  case $operatingsystem {
    centos, fedora: {
      $ssh_service  = "sshd"
      $sshd_config  = "/etc/ssh/sshd_config"
      $ssh_packages = [ "openssh"
                      , "openssh-server"
                      , "openssh-clients" ]
    }

    Solaris: {
      $ssh_service  = "network/ssh"
      $sshd_config  = "/etc/ssh/sshd_config"
      $ssh_packages = [ "pkg:/network/ssh"
                      , "pkg:/network/ssh/ssh-key"
                      , "pkg:/service/network/ssh"
                      # This fails at the moment on bite.entic.net
                      #, "pkg:/system/library/iconv/utf-8"
                      ]

      Package[$ssh_packages] { provider => pkg }

      # On some Solaris systems, the following is necessary to allow root
      # logins:
      #  rolemod -K type=normal root

      exec { "allow non-console root logins":
        user    => root,
        command => "perl -i -pe 's/^CONSOLE/#CONSOLE/;' /etc/default/login",
        onlyif  => "grep '^CONSOLE' /etc/default/login";
      }
    }

    Darwin: {
      $ssh_service  = "sshd"
      $sshd_config  = "/etc/sshd_config"
      $ssh_packages = [ "openssh" ]
    }

    default: {
      $ssh_service  = "sshd"
      $sshd_config  = "/etc/ssh/sshd_config"
      $ssh_packages = [ "ssh" ]
    }
  }

  package { $ssh_packages: ensure => latest }

  file { "/root/.ssh":
    owner   => root,
    group   => root,
    mode    => 0700,
    ensure  => directory;
  }

  augeas { sshd_config:
    context => '/files/etc/ssh/sshd_config',
    # permit root logins only using publickey
    changes => 'set PermitRootLogin without-password',
    onlyif  => 'get PermitRootLogin != without-password',
    notify  => Service['sshd'],
    require => Package[$ssh_packages];
  }

  service { sshd:
    name       => $ssh_service,
    ensure     => running,
    enable     => true,
    hasstatus  => true,
    hasrestart => true,
    require    => Augeas[sshd_config];
  }

  tcpwrapper::rule { sshd: allow => "ALL" }

  #nagios::target::service { sshd: }
  #nagios::service { check_ssh: }

  #firewall::rule_tmpl { sshd: }
}
