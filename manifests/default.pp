class repositories {

  file{'/etc/apt/sources.list.d/webupd8team-java-trusty.list':
    content => 'deb http://ppa.launchpad.net/webupd8team/java/ubuntu trusty main'
  }

  file{'/etc/apt/sources.list.d/sbt.list':
    content => 'deb http://dl.bintray.com/sbt/debian /'
  }

  file{'/etc/apt/trusted.gpg.d':
    ensure => 'directory'
  }

  file{'/etc/apt/trusted.gpg.d/webupd8team-java.gpg':
    source => '/vagrant/vm/webupd8team-java.gpg'
  }

  exec{'accept-oracle-license':
    command => '/bin/echo debconf shared/accepted-oracle-license-v1-1 select true | debconf-set-selections'
  }

}

class packages {
  $pkgs = [ "curl",
            "software-properties-common",
            "docker.io",
            "git",
            "vim",
            "build-essential",
            "autoconf",
            "facter",
            "oracle-java8-installer",
            "sbt" ]

  package{$pkgs:
    ensure => latest,
    # The SBT package is not signed
    install_options => [ '--force-yes' ]
  }

  file{'/etc/default/docker.io':
    require => Package['docker.io'],
    content => 'DOCKER_OPTS="-H tcp://127.0.0.1:2375 -H tcp://127.0.0.1:4243 -H unix:///var/run/docker.sock"'
  }
}

include repositories
include packages
Class['repositories'] ~> exec{'/usr/bin/apt-get update -q': } ~> Class['packages']


# cd src
# git clone --depth=1 https://github.com/epfl-lara/ScalaZ3.git
# cd ScalaZ3
# git checkout 3b5c1872e7b7a98fe5389c82ca2545a5dad59820

# unzip ~/src/$Z3.zip
# mv $Z3 4.3-unix-64b
# mv