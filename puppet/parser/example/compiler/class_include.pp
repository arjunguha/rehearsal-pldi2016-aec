class myclass {

  file {'/tmp/file': ensure => present}
  package {'git': ensure => installed}
}

include myclass
