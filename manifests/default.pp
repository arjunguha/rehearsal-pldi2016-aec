$pkgs = [ "lubuntu-core",
          "lxterminal",
          "xdg-utils",
          "curl",
          "software-properties-common",
          "docker.io",
          "git",
          "build-essential",
          "autoconf",
          "facter" ]

package{$pkgs:
  ensure => latest
}

file{'/etc/default/docker.io':
  require => Package['docker.io'],
  content => 'DOCKER_OPTS="-H tcp://127.0.0.1:2375 -H tcp://127.0.0.1:4243 -H unix:///var/run/docker.sock"'
}



exec{'add-java-repo':
  require => Package['software-properties-common'],
  refreshonly => 'true',
  command => '/usr/bin/add-apt-repository ppa:webupd8team/java'
}

exec{'accept-oracle-license':
  require => Exec['add-java-repo'],
  command => '/bin/echo debconf shared/accepted-oracle-license-v1-1 select true | debconf-set-selections'
}

exec{'update':
  require => Exec['accept-oracle-license'],
  refreshonly => 'true',
  command => '/usr/bin/apt-get update -q'
}

package{'oracle-java8-installer':
  ensure => latest
}

exec{'download-sbt':
  command => '/usr/bin/wget -q http://dl.bintray.com/sbt/debian/sbt-0.13.5.deb',
  cwd => '/root',
  creates => '/root/sbt-0.13.5.deb'
}

exec{'download-idea':
  command => '/usr/bin/wget -q http://download.jetbrains.com/idea/ideaIC-13.1.4b.tar.gz',
  cwd => '/root',
  creates => '/root/ideaIC-13.1.4b.tar.gz'
}

file{'/opt':
  ensure => directory
}

file{'/etc/lightdm/lightdm.conf':
  source => '/vagrant/vm/lightdm.conf',
  require => Package['lubuntu-core']
}

file{'/usr/share/pixmaps/idea.png':
  source => '/opt/idea-IC-135.1230/bin/idea.png',
  require => Exec['install-idea']
}

exec{'idea-shortcut':
  command => '/usr/bin/desktop-file-install /vagrant/vm/idea.desktop',
  require => Exec['install-idea']
}

exec{'install-idea':
  require => [ Exec['download-idea'], File['/opt'] ],
  cwd => '/root',
  command => '/bin/tar xz -C /opt -f ideaIC-13.1.4b.tar.gz',
  creates => '/opt/idea-IC-135.1230'
}

package{'sbt':
  provider => dpkg,
  ensure => present,
  require => Exec['download-sbt'],
  source => '/root/sbt-0.13.5.deb'
}





# cd src
# git clone --depth=1 https://github.com/epfl-lara/ScalaZ3.git
# cd ScalaZ3
# git checkout 3b5c1872e7b7a98fe5389c82ca2545a5dad59820

# unzip ~/src/$Z3.zip
# mv $Z3 4.3-unix-64b
# mv