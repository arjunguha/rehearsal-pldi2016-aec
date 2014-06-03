class java {
  exec { "Register ppa:webupd8team/java":
    require => Package["python-software-properties"],
    command => "apt-add-repository ppa:webupd8team/java -y &&
                apt-get update",
    creates => "/etc/apt/sources.list.d/webupd8team-java-${::lsbdistcodename}.list",
  }
  ->
  exec { "Accept Oracle License":
    command => "echo debconf shared/accepted-oracle-license-v1-1 select true | debconf-set-selections &&
                echo debconf shared/accepted-oracle-license-v1-1 seen true | debconf-set-selections",
    unless => "sudo debconf-get-selections | grep accepted-oracle-license-v1-1 | grep -q true",
  }
  ->
  package { "oracle-java7-installer":
    ensure => present
  }
}
