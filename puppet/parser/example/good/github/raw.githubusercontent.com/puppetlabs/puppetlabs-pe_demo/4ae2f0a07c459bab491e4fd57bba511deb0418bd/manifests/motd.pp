# Demo: MOTD
# This class creates a MOTD in /etc/motd that changes every Puppet run based
# on varying memoryfree and uptime facts.
class pe_demo::motd {

  # Demo: Changing Resources
  ## Create a unique /etc/motd file on each machine that will change on each run

  $random_number = fqdn_rand(3000,30)

  file { "/etc/motd":
    ensure  => file,
    content => "There are ${pe_demo::motd::random_number} reasons to love Puppet!\n\nWelcome to ${::fqdn} which has ${::memoryfree} of free memory and has been up for ${::uptime}.\n",    owner => 'root',
    group => 'root',
    mode  => '0600',
  }

}
