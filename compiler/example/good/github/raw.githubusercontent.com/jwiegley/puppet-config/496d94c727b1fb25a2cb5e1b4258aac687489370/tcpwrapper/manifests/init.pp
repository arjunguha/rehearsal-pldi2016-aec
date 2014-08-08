define tcpwrapper::rule ($allow = "", $deny = "")
{
  if $allow {
    exec { "tcpwrapper-allow-$title":
      command => "echo '$title : $allow' >> /etc/hosts.allow",
      unless  => "grep ^'$title : $allow' /etc/hosts.allow";
    }
  } else {
    exec { "tcpwrapper-deny-$title":
      command => "echo '$title : $deny' >> /etc/hosts.deny",
      unless  => "grep ^'$title : $allow' /etc/hosts.deny";
    }
  }
}
