define asterisk::function::registration(
  $context,
  $secret,
  $domain = '',
  $extension = '',
  $template = 'ksp-itsp',
) {
  require asterisk::server

  $base = "${asterisk::params::basedir}/sip.conf.d/registrations"
  $ast_template = $template

  $split = split($name, '@')
  $user = $split[0]
  $host = $split[1]

  file { "$base/${name}.conf":
    ensure  => present,
    content => template('asterisk/etc/asterisk/sip.conf.d/registrations/template.conf.orig.erb'),
    notify  => Exec['asterisk-module-reload-sip.conf'],
    require => File[$base],
  }
}

# vim:sw=2:ts=2:expandtab
