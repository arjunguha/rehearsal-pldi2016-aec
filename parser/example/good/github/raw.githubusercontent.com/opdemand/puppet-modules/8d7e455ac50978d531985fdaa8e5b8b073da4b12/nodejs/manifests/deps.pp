class nodejs::deps {

  # define local vars
  $username = "$nodejs::params::username"
  $group = "$nodejs::params::group"
  $repository_path = "$nodejs::params::repository_path"
  
  # exec bin/deploy if the repo changed
  exec { "bin::deploy":
    command => "$repository_path/bin/deploy",
    # log raw output from shell command
    logoutput => true,
    cwd => $repository_path,
    path => ["/sbin", "/bin", "/usr/bin", "/usr/local/bin"],
    user => $username,
    group => $group,
    require => [Class[Nodejs::Install], Class[Nodejs::Config] ],
    subscribe => Vcsrepo[$repository_path],
    # only if the script exists and is executable
    onlyif => "test -x $repository_path/bin/deploy",
  }
  
  # npm install
  exec { "npm::install":
    command => "sudo -u $username npm install",
    cwd => $repository_path,
    path => ["/sbin", "/bin", "/usr/bin", "/usr/local/bin"],
    user => $username,
    group => $group,
    require => Exec["bin::deploy"],
    subscribe => Vcsrepo[$repository_path],
  }
  
}
