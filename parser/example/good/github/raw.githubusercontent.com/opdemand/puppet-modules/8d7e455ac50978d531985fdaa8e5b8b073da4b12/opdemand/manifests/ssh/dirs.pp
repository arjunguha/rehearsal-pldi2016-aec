
class opdemand::ssh::dirs {

  file {"/root/.ssh":
    owner => "root",
    group => "root",
    mode => 0700,
    ensure => directory,
  }

  file {"/home/ubuntu/.ssh":
    owner => "ubuntu",
    group => "ubuntu",
    mode => 0700,
    ensure => directory,
  }
}