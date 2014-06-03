class system::ntpd {
    package { "ntpdate.x86_64": 
      ensure => installed 
    }
    service { "ntpd":
      ensure => running,
    }
}