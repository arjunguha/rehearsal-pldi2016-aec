define freebsd::network::lagg (
  $laggproto = 'lacp',
  $laggports = [],
  $mtu       = ''
) {

  # This code creates the configuration for an LACP bundle interface.  It could
  # eventually manage the creation and destruction of the interface and its
  # parameters.

  # Set the MTU of the LAGG interface.
  if ($mtu != '') {
    freebsd::network::interface { $laggports: mtu => $mtu; }
  }

  # Build up the lagg interface string here for simplicity
  $lagg_string = inline_template("laggproto ${laggproto} laggport <%= laggports.join(' laggport ') %> up")

  # Add the ifconfig line to rc.conf
  shell_config { "configure_lagg_${name}":
    file  => '/etc/rc.conf',
    key   => "ifconfig_${name}",
    value => "${lagg_string}"
  }
}
