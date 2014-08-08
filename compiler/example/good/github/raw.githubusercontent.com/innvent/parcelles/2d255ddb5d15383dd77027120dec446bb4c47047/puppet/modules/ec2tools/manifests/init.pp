class ec2tools {
  exec { "Register ppa:alestic":
    require => Package["python-software-properties"],
    before => Package["ec2-consistent-snapshot"],
    command => "apt-add-repository ppa:alestic -y &&
                apt-get update",
    creates => "/etc/apt/sources.list.d/alestic-ppa-${::lsbdistcodename}.list",
  }

  package { [ "liblocal-lib-perl", "ec2-consistent-snapshot" ]:
    ensure => latest
  }

  # Perl Deps for ec2-consistent-snapshot
  require cpan
  $cpan_deps = [ Package["liblocal-lib-perl"], Package["build-essential"], Package["unzip"] ]
  cpan { [ "Net::Amazon::EC2", "Any::Moose" ]:
    require => $cpan_deps,
    ensure => present
  }

  if defined(Package["mongodb-10gen"]) {
    $cpan_deps += [ Package["mongodb-10gen"] ]
    cpan { "MongoDB::Admin":
      require => $cpan_deps,
      ensure => present
    }
  }

  # EC2 api tools
  require java
  $ec2_api_tools = "http://s3.amazonaws.com/ec2-downloads/ec2-api-tools.zip"
  exec { "Install ec2-api-tools":
    command => "wget ${ec2_api_tools} &&
                unzip ec2-api-tools.zip &&
                echo 'mv $(compgen -A file ec2-api-tools-) /home/ubuntu/ec2/' | bash &&
                rm ec2-api-tools.zip",
    creates => "/home/ubuntu/ec2",
    user => "ubuntu"
  }
}
