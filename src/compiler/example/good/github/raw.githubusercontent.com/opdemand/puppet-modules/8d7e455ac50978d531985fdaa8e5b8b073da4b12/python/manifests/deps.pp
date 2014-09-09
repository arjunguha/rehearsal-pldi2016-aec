class python::deps {

  # local variables
  $repository_path = $python::params::repository_path
  $username = $python::params::username
  $group = $python::params::group
  $virtualenv_path = "$python::params::repository_path/venv"
  
  # exec bin/deploy if the repo changed
  exec { "bin::deploy":
    command => "$repository_path/bin/deploy",
    # log raw output from shell command
    logoutput => true,
    cwd => $repository_path,
    path => ["/sbin", "/bin", "/usr/bin", "/usr/local/bin"],
    user => $username,
    group => $group,
    require => [Class[Python::Install], Class[Python::Config] ],
    subscribe => Vcsrepo[$repository_path],
    # only if the script exists and is executable
    onlyif => "test -x $repository_path/bin/deploy",
  }

  # pip install
  exec { "pip::install":
    command => "/bin/bash -c 'source $virtualenv_path/bin/activate && pip install -r requirements.txt'",
    cwd => $repository_path,
    user => $username,
    group => $group,
    require => Exec["bin::deploy"],
    subscribe => Vcsrepo[$repository_path],
  }
  
}