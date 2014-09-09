define jenkins::job($jobfile, $user = 'aegir', $destination='/var/lib/jenkins') {
  file { "$destination/jobs/$name":
    ensure => directory,
    owner => $user
  }

  file { "$destination/jobs/$name/config.xml":
    source => $jobfile,
    owner => $user,
    require => [File["$destination/jobs"], File["$destination/jobs/$name"]],
    notify => Service["jenkins"],
    replace => false
  }
}
