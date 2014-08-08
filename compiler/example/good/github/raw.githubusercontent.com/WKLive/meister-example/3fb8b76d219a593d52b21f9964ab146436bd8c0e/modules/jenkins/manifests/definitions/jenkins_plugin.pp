define jenkins::plugin($user = 'jenkins', $destination='/var/lib/jenkins/plugins', $version = 'latest') {
  exec { "install-jenkins-plugin-$name":
    cwd => $destination,
    command => "/bin/su $user -c \"/usr/bin/wget http://updates.jenkins-ci.org/latest/${name}.hpi\"",
    creates => "$destination/$name",
    notify => Service['jenkins'],
    require => File[$destination],
  }
}
