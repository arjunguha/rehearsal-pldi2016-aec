class kbp_icinga2::server {
  include gen_icinga2::server
}

class kbp_icinga2::classicui {
  include gen_icinga2::classicui

  concat { '/etc/icinga2/classicui/.htpasswd':
    require => Package['icinga2-classicui'];
  }

  Concat::Add_content <<| tag == 'htpasswd' |>> {
    target => '/etc/icinga2/classicui/.htpasswd',
  }
}
