class ruby::deps {

  # local variables
  $repository_path = "$ruby::params::repository_path"
  $username = "$ruby::params::username"
  $group = "$ruby::params::group"
  
  # exec bin/deploy if the repo changed
  exec { "bin::deploy":
    command => "$repository_path/bin/deploy",
    # log raw output from shell command
    logoutput => true,
    cwd => $repository_path,
    path => ["/sbin", "/bin", "/usr/bin", "/usr/local/bin"],
    user => $username,
    group => $group,
    require => [Class[Ruby::Install], Class[Ruby::Config] ],
    subscribe => Vcsrepo[$repository_path],
    # only if the script exists and is executable
    onlyif => "test -x $repository_path/bin/deploy",
  }
    
  # bundle install latest dependencies
  exec { "bundle-install":
    command => "bundle install --deployment",
    path => ["/sbin", "/bin", "/usr/bin", "/usr/sbin", "/usr/local/bin"],
    cwd => $repository_path,
    user => $username,
    group => $group,
    require => Exec["bin::deploy"],
    subscribe => Vcsrepo[$repository_path],
  }

}