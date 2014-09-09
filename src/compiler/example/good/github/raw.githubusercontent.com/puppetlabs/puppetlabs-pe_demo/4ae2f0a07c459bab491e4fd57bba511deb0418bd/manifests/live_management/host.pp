# Demo: Host variance
## Creates a host entry to clone around.
## The IP addresses are not real.
class pe_demo::live_management::host {

  $random_host_choice = fqdn_rand(5)

  $host = $random_host_choice ? {
    '0' => 'elmo.puppetlabs.com',
    '1' => 'beaker.puppetlabs.com',
    '2' => 'kermit.puppetlabs.com',
    '3' => 'gonzo.puppetlabs.com',
    '4' => 'statler.puppetlabs.com'
  }

  host { $host:
    ensure       => present,
    ip           => "192.168.121.${random_host_choice}",
    host_aliases => ['muppet','conference_room'],
  }

}
