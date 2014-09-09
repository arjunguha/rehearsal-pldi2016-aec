class clojure::deps {

  # define local vars
  $username = "$clojure::params::username"
  $group = "$clojure::params::group"
  $repository_path = "$clojure::params::repository_path"

  # exec bin/deploy if the repo changed
  exec { "bin::deploy":
    command => "$repository_path/bin/deploy",
    # log raw output from shell command
    logoutput => true,
    cwd => $repository_path,
    path => ["/sbin", "/bin", "/usr/bin", "/usr/local/bin"],
    user => $username,
    group => $group,
    require => [Class[Clojure::Install], Class[Clojure::Config] ],
    subscribe => Vcsrepo[$repository_path],
    # only if the script exists and is executable
    onlyif => "test -x $repository_path/bin/deploy",
  }
  
  # install leinengen deps
  exec { "lein::deps":
    command => "lein deps",
    cwd => $repository_path,
    path => ["/sbin", "/bin", "/usr/bin", "/usr/local/bin"],
    user => $username,
    group => $group,
    subscribe => Vcsrepo["$repository_path"],
    require => Exec["bin::deploy"],
  }
  
}