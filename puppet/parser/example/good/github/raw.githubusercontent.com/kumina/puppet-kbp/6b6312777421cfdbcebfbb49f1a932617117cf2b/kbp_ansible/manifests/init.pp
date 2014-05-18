define kbp_ansible::client($ensure='present') {
  if $lsbdistcodename == 'lenny' {
    notify { 'No support for Ansible on Lenny.':; }
  } else {
    include gen_base::python_keyczar

    if $ensure == 'present' {
      Group <<| tag == 'ansible_client' |>>
      Kbp_user <<| tag == 'ansible_client' |>>
      Kbp_ferm::Rule <<| tag == 'ansible_client' |>>
    }
  }
}

class kbp_ansible::server($key, $username, $uid, $gid, $password, $password_hash, $desc) {
  file { '/etc/ansible/pass':
    content => $password,
    owner   => $username,
    mode    => 400;
  }

  @@group { $username:
    gid => $gid,
    tag => 'ansible_client';
  }

  @@kbp_user { $username:
    uid      => $uid,
    gid      => $username,
    comment  => $desc,
    keys     => $key,
    password => $password_hash,
    tag      => 'ansible_client';
  }

  @@concat::add_content { "Add ${username} to Kumina SSH keyring":
    target  => '/etc/ssh/kumina.keys',
    content => "# ${username}\nssh-rsa ${key}";
  }

  kbp_ferm::rule { 'Allow accelerated access from ansible server':
    saddr    => $ipaddress_eth0,
    dport    => 5099,
    proto    => 'tcp',
    action   => 'ACCEPT',
    ferm_tag => 'ansible_client';
  }
}
