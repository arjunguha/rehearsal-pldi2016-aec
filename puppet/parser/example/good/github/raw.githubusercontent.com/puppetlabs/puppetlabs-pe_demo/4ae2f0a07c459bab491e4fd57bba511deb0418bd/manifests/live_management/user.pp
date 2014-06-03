define pe_demo::live_management::user {

  # Demo: User variance
  ## Create users with different shells for use in live management.

  $random_shell_choice = fqdn_rand(4)

  $shell = $random_shell_choice ? {
    '0' => '/bin/bash',
    '1' => '/bin/ksh',
    '2' => '/bin/sh',
    '3' => '/sbin/nologin',
  }

  user { $name:
    ensure     => present,
    home       => "/home/${name}",
    shell      => $shell,
  }

  if ! defined ( Group[$name] ) {
    group { $name:
      ensure => $ensure,
    }
  }

}
