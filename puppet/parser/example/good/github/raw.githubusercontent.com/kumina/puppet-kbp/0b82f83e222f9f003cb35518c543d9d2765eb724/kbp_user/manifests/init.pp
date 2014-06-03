class kbp_user::environment {
  Kbp_user::Hashfragment <<| tag == 'generic_htpasswd' |>>
}

class kbp_user::admin_users {
  Kbp_user::Admin_user <<| tag == 'admin_user' |>>
}

define kbp_user($ensure="present", $uid, $gid, $comment, $groups=false, $shell='/bin/bash', $keys=false, $key_type='ssh-rsa', $passwords=false, $password=false, $home = "/home/${name}") {
  user { $name:
    ensure     => $ensure,
    uid        => $uid,
    gid        => $gid,
    groups     => $groups ? {
      false   => undef,
      default => $groups,
    },
    shell      => $shell,
    comment    => $comment,
    home       => $home,
    managehome => true,
    password   => $password ? {
      false   => undef,
      default => $password,
    };
  }

  if $keys and $ensure == "present" {
    kbp_user::expand_keys { $keys:
      user => $name,
      type => $key_type;
    }
  }

  $ensure_directory = $ensure ? {
    'present' => 'directory',
    default   => $ensure,
  }

  file { $home:
    ensure => $ensure_directory,
    mode   => 750,
    owner  => $name,
    group  => $gid,
    force  => true;
  }
}

define kbp_user::admin_user($ensure='present', $comment, $uid, $gid, $groups=false, $shell, $passwords, $key, $key_type='ssh-rsa', $files=false) {
  kbp_user { $name:
    ensure   => $ensure,
    comment  => $comment,
    uid      => $uid,
    gid      => $gid,
    groups   => $groups,
    shell    => "/bin/${shell}",
    password => $passwords[$environment],
    keys     => $key,
    key_type => $key_type;
  }

  $ensure_directory = $ensure ? {
    'present' => 'directory',
    default   => $ensure,
  }

  file {
    "/home/${name}/.ssh":
      ensure  => $ensure_directory,
      mode    => 700,
      owner   => $name,
      group   => $gid;
    "/home/${name}/.tmp":
      ensure  => $ensure_directory,
      owner   => $name,
      group   => $gid;
    "/home/${name}/.reportbugrc":
      ensure  => $ensure,
      content => "email ${name}@kumina.nl\n",
      owner   => $name,
      group   => $gid;
  }

  if $ensure == 'present' {
    gen_postfix::alias { "${name}: ${name}@kumina.nl":; }

    concat::add_content { "Add ${name} to Kumina SSH keyring":
      target  => "/etc/ssh/kumina.keys",
      content => "# ${comment} <${name}@kumina.nl>\n${key_type} ${key}";
    }
  }

  if $files and $ensure == 'present' {
    create_resources(file, $files)
  }
}

define kbp_user::expand_keys($user, $type='ssh-rsa') {
  ssh_authorized_key { "${user}_${name}":
    user => $user,
    key  => $name,
    type => $type;
  }
}

define kbp_user::hashfragment($hash) {
  @@concat::add_content { "${hash}_${environment}":
    content => $hash,
    tag     => $environment ? {
      "kumina" => ["htpasswd","htpasswd_${environment}"],
      default  => "htpasswd_${environment}",
    };
  }
}
