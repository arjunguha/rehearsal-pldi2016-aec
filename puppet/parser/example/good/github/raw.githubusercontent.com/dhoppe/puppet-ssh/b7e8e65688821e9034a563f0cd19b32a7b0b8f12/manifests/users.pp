define ssh::users($group) {
  $group_real = $group ? {
    'undef' => $name,
    default => $group,
  }

  file { "/home/${name}":
    ensure => directory,
    owner  => $name,
    group  => $group_real,
    mode   => '0755',
  }

  file { "/home/${name}/.ssh":
    ensure => directory,
    owner  => $name,
    group  => $group_real,
    mode   => '0700',
  }

  file { "/home/${name}/.ssh/authorized_keys":
    owner  => $name,
    group  => $group_real,
    mode   => '0600',
    source => [
      "puppet:///modules/ssh/common/users/.ssh/${name}_dsa.pub",
      "puppet:///modules/ssh/common/users/.ssh/${name}_rsa.pub"
    ],
  }
}