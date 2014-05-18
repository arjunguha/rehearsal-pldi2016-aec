class jetty::deps {

  # local variables
  $repository_path = $jetty::params::repository_path
  $username = $jetty::params::username
  $group = $jetty::params::group
  $virtualenv_path = "$jetty::params::repository_path/venv"
  
  # exec bin/deploy if the repo changed
  exec { "bin::deploy":
    command => "$repository_path/bin/deploy",
    # log raw output from shell command
    logoutput => true,
    cwd => $repository_path,
    path => ["/sbin", "/bin", "/usr/bin", "/usr/local/bin"],
    user => $username,
    group => $group,
    require => [Class[Jetty::Install], Class[Jetty::Config] ],
    subscribe => Vcsrepo[$repository_path],
    # only if the script exists and is executable
    onlyif => "test -x $repository_path/bin/deploy",
  }

  exec { "maven::package":
    command => "mvn package",
    cwd => $repository_path,
    user => $username,
    group => $group,
    require => Exec["bin::deploy"],
    subscribe => Vcsrepo[$repository_path],
  }
  
}