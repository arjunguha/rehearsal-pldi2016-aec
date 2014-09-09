class kbp_squirrelmail {
  include gen_squirrelmail
  include gen_squirrelmail::plugin::avelsieve
}

define kbp_squirrelmail::site ($cert=false, $intermediate=false, $wildcard=false, $address='*', $serveralias=false, $org_name=false, $org_logo=false, $org_logo_width=false, $org_logo_height=false, $org_title=false, $provider_uri=false, $monitor_path=false) {
  include kbp_squirrelmail

  kbp_apache::site { $name:
    cert         => $cert,
    wildcard     => $wildcard,
    intermediate => $intermediate,
    address      => $address,
    serveralias  => $serveralias,
    documentroot => '/usr/share/squirrelmail',
    php          => true,
    monitor_path => $monitor_path;
  }

  file { "/etc/squirrelmail/config_local.php":
    content => template("kbp_squirrelmail/config_local.php"),
    require => Package["squirrelmail"];
  }

  kbp_apache::vhost_addition { "${name}/javascript":
    ports   => '443',
    content => "Alias /javascript /usr/share/javascript\n";
  }
}
