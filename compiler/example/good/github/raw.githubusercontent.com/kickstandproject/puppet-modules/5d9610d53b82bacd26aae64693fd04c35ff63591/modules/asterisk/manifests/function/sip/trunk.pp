define asterisk::function::sip::trunk(
  $options = {}
) {
  require asterisk::server

  $defaults = {
    'type'     => 'peer',
    'host'     => 'dynamic',
    'context'  => 'from-itsp',
    'template' => 'ksp-itsp'
  }

  $options_real = merge($defaults, $options)
  $name_real = $name

  if ($options_real['secret']) {
    $options_real['md5secret'] = md5("${name}:asterisk:${options_real['secret']}")
  }

  file { "${asterisk::params::server::basedir}/sip.conf.d/trunks/${name}.conf":
    ensure  => file,
    content => template('asterisk/etc/asterisk/sip.conf.d/trunks/template.conf.erb'),
    notify  => Exec['asterisk-module-reload-sip.conf'],
    require => File["${asterisk::params::server::basedir}/sip.conf.d/trunks"],
  }
}

# vim:sw=2:ts=2:expandtab
