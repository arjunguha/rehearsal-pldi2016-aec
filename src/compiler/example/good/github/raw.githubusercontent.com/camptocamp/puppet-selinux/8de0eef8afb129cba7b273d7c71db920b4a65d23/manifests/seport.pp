# == Definition: selinux::seport
#
# Adds/removes ports to SELinux security contexts.
#
# Parameters:
#
# - *$name*: security context name
# - *$ensure*: present/absent
# - *$proto*: tcp/udp
# - *$port*: port number to add/remove from security context
# - *$setype*: specify the selinux type, in case $name can't be used
#
# Example usage:
#
#   # allow apache to bind on port 8001
#   selinux::seport { "http_port_t":
#     ensure => present,
#     proto  => "tcp",
#     port   => "8001",
#     before => Service["apache"],
#   }
#
define selinux::seport($port, $ensure='present', $proto='tcp', $setype=undef) {

  # this is dreadful to read, sorry...

  if $ensure == 'present' {
    $mgt  = '--add'
    $grep = 'egrep -q'
  } else {
    $mgt  = '--delete'
    $grep = '! egrep -q'
  }

  if $setype == undef {
    $type = $name
  } else {
    $type = $setype
  }

  $re = "^${type}\W+${proto}\W+.*\W${port}(\W|$)"

  exec { "semanage port ${port}, proto ${proto}, type ${name}":
    command => "semanage port ${mgt} --type ${type} --proto ${proto} ${port}",
    # subshell required to invert return status with !
    unless  => "semanage port --list | ( ${grep} '${re}' )",
  }

}
