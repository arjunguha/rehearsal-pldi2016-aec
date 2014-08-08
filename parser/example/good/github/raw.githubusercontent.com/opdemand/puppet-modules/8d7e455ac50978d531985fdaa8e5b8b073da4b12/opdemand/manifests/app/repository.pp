class opdemand::app::repository (
  
  # inputs default to hiera lookup followed by second arg
  # can override using parameterized class inputs
  $repository_provider = hiera("application/repository_provider", "git"),
  $repository_key = hiera("application/repository_key", ""),
  $repository_url = hiera("application/repository_url"),
  $repository_path = hiera("application/repository_path", "/home/ubuntu/repo"),
  $repository_revision = hiera("application/repository_revision", "master"),
  $repository_owner = hiera("application/username", "ubuntu"),
  $repository_group = hiera("application/group", "ubuntu")) {

  # require common including ssh classes
  require opdemand::common
  
  # determine ssh identity file to use
  if $repository_key {
    $identity_path = "/home/ubuntu/.ssh/opdemand-app"
  } else {
    $identity_path = "/dev/null"
  }
  
  # manage a version control repository
  vcsrepo { $repository_path:
    ensure => latest,
    provider => $repository_provider,
    source => $repository_url,
    # NOTE: as of 2012/4/12 this only works on initial clone
    revision => $repository_revision,
    owner => $repository_owner,
    group => $repository_group,
    require => [ Class["Opdemand::Ssh::Known_hosts"], Class["Opdemand::Ssh::Private_keys"] ],
    identity => $identity_path,
  }

  # manage the repository directories
  file { $repository_path:
    ensure => directory,
    owner => $repository_owner,
    group => $repository_group,
    mode => 0750,
    require => Vcsrepo[$repository_path],
  }
  
}
