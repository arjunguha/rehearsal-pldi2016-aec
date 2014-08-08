class custom::deps {

  # local variables
  $repository_path = $custom::params::repository_path
  $username = $custom::params::username
  $group = $custom::params::group
  
  # exec bin/deploy if the repo changed
  exec { "bin::deploy":
    command => "$repository_path/bin/deploy",
    # log raw output from shell command
    logoutput => true,
    cwd => $repository_path,
    path => ["/sbin", "/bin", "/usr/bin", "/usr/local/bin"],
    user => $username,
    group => $group,
    require => Vcsrepo[$repository_path],
    subscribe => Vcsrepo[$repository_path],
  }
  
}
