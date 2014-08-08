# Author: Kumina bv <support@kumina.nl>

# Class: kbp_samba::server
#
# Actions:
#  Setup a samba server.
#
# Parameters:
#  bindaddress: The address or interface to bind on. Set to false to bind to all interfaces (unsafe!). Defaults to 'lo'.
#  servername: The name of the server. Defaults to '$hostname'.
#  workgroup: The name of the workgroup for this server. Defaults to 'KUMINA'.
#  open_firewall_for: An IP address or range (in ferm format) to open up the firewall for per default. Defaults to false, which doesn't
#                     open the firewall for a range.
#
# Depends:
#  gen_samba
#  gen_ferm
#
class kbp_samba::server ($servername=$hostname, $workgroup='KUMINA', $bindaddress='lo', $open_firewall_for=false) {
  include kbp_munin::client::samba
  include kbp_icinga::samba
  class { 'gen_samba::server':
    servername  => $servername,
    workgroup   => $workgroup,
    bindaddress => $bindaddress;
  }

  if $open_firewall_for {
    kbp_ferm::rule {
      "Samba traffic (netbios-ns, netbios-dgm)":
        proto     => "udp",
        saddr     => $open_firewall_for,
        dport     => "(137 138)",
        action    => "ACCEPT";
      "Samba traffic (netbios-ssn, microsoft-ds)":
        proto     => "tcp",
        saddr     => $open_firewall_for,
        dport     => "(139 445)",
        action    => "ACCEPT";
    }
  }
}

# Define: kbp_samba::share
#
# Actions: Setup a share in Samba.
#
# Parameters:
#  name: Name of the share.
#  dir: The directory to share under this name.
#  comment: The long, pretty name for this share. Browser can see this. Defaults to the $name.
#  readonly: Whether the share should be read-only. Defaults to true.
#  createmask: The permissions to set on new files. Defaults to 0664.
#  directorymask: The permissions to set on new directories. Defaults to 0775.
#  browseable: If the share should be visible if a visitor just connects to the server. Defaults to false.
#
# Depends:
#  gen_samba
#
define kbp_samba::share ($dir, $comment=$name, $readonly=true, $createmask='0664', $directorymask='0775', $browseable=false) {
  gen_samba::share { $name:
    dir           => $dir,
    comment       => $comment,
    readonly      => $readonly,
    createmask    => $createmask,
    directorymask => $directorymask,
    browseable    => $browseable;
  }
}

# Define: kbp_samba::user
#
# Action: Setup a user to use the samba share. This requires a system user with the same name!
#
# Parameters:
#  name: Username of the Samba user.
#  ensure: Whether the user should be present or absent. Defaults to 'present'.
#  password: The password to use for this Samba user. Yes, it's pretty bad to put it in the puppet code, but I don't have a better way currently.
#
define kbp_samba::user ($ensure='present',$password) {
  gen_samba::user { $name:
    ensure   => $ensure,
    password => $password;
  }

  include gen_samba::clean
}
