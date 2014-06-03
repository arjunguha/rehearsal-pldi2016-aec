define asterisk::function::sip::registration(
  $secret,
  $domain = '',
  $extension = '',
) {
  require asterisk::server

  $base = "${asterisk::params::basedir}/sip.conf.d/registrations"

  $split = split($name, '@')
  $user = $split[0]
  $host = $split[1]

  file { "$base/${name}.conf":
    ensure  => file,
    content => template('asterisk/etc/asterisk/sip.conf.d/registrations/template.conf.erb'),
    notify  => Exec['asterisk-module-reload-sip.conf'],
    require => File[$base],
  }
}

# vim:sw=2:ts=2:expandtab
