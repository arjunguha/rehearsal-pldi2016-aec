class myclass {

  file {'/tmp/myfile': ensure => present}
  package {'SomeGit': ensure => installed}
}

class {'myclass':}
