class kbp_ssl::intermediate::rapidssl {
  kbp_ssl::intermediate { 'rapidssl':; }
}

class kbp_ssl::intermediate::terena {
  kbp_ssl::intermediate { 'terena':; }
}

class kbp_ssl::intermediate::positivessl {
  kbp_ssl::intermediate { 'positivessl':; }
}

class kbp_ssl::intermediate::thawte {
  kbp_ssl::intermediate { 'thawte':; }
}

class kbp_ssl::intermediate::verisign {
  kbp_ssl::intermediate { 'verisign':; }
}

class kbp_ssl::intermediate::kumina {
  kbp_ssl::intermediate { 'kumina':; }
}

class kbp_ssl::intermediate::godaddy {
  kbp_ssl::intermediate { 'godaddy':; }
}

define kbp_ssl::keys($owner = 'root') {
  $key_name = regsubst($name,'^(.*)/(.*)$','\2')

  kbp_ssl::private_key { $key_name:
    key_location => "${name}.key",
    owner        => $owner;
  }

  kbp_ssl::public_key { $key_name:
    key_location => "${name}.pem",
    owner        => $owner;
  }
}

define kbp_ssl::public_key($content=false, $key_location=false, $owner='root') {
  file { "/etc/ssl/certs/${name}.pem":
    content => $content ? {
      false   => template($key_location),
      default => $content,
    },
    owner   => $owner,
    mode    => 444;
  }

  kbp_icinga::sslcert { $name:; }
}

define kbp_ssl::private_key($key_location=false, $owner='root') {
  file { "/etc/ssl/private/${name}.key":
    source => "puppet:///modules/${key_location}",
    owner  => $owner,
    mode   => 400;
  }
}

define kbp_ssl::intermediate {
  $intermediate = $name
  $realname = template("kbp_ssl/translate_names.erb")

  if defined(Exec['reload-apache2']) {
    $notify_apache = true
  } else {
    $notify_apache = false
  }

  kbp_ssl::public_key { $realname:
    key_location => "kbp_ssl/${realname}.pem",
    notify       => $notify_apache ? {
      false => undef,
      true  => Exec['reload-apache2'],
    };
  }
}
