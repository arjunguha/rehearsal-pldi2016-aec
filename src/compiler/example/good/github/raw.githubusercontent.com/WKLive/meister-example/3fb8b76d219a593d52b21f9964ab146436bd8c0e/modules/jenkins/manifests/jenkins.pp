# Jenkins specification.
class jenkins ($port = '8180', $jenkins_user = 'aegir', $control_user = false) {
  package { 'jenkins':
    ensure => present,
    require => User[$jenkins_user],
  }
  service { 'jenkins':
    ensure => running,
    require => Package['jenkins'],
  }
  if $control_user {
    user { $jenkins_user:
      ensure => "present",
      comment => "A jenkins user",
      home => '/var/lib/jenkins',
      shell  => '/bin/bash',
      groups => "shadow",
      require => Package['jenkins']
    }
  }
  # If we are using a non-standard jenkins user,
  # we need to make sure it is owned by that user.
  file { "/var/lib/jenkins":
    ensure => directory,
    owner => $jenkins_user,
    notify => Service['jenkins'],
    require => Package['jenkins']
  }
  file { "/var/log/jenkins":
    ensure => directory,
    owner => $jenkins_user,
    notify => Service['jenkins'],
    require => Package['jenkins']
  }
  file { "/var/lib/jenkins/jobs":
    ensure => directory,
    owner => $jenkins_user
  }
  exec { "jenkins-fix-permissions":
    command => "/bin/chown -R $jenkins_user /var/lib/jenkins; /bin/chown -R $jenkins_user /var/log/jenkins",
    require => Package['jenkins']
  }

  # The Jenkins group is used for people who should have access to jenkins.
  group { "jenkins":
    ensure => present
  }
  # A base config.xml
  file { "/var/lib/jenkins/config.xml":
    source => "puppet:///modules/jenkins/config.xml",
    ensure => present,
    require => Package['jenkins'],
    owner => $jenkins_user
  }

  file { "/etc/default/jenkins":
    content => template("jenkins/default.erb"),
    ensure => present,
    require => Package['jenkins'],
    owner => 'root'
  }

  file { "/var/lib/jenkins/plugins":
    ensure => directory,
    require => Package['jenkins'],
    owner => $jenkins_user
  }
  # Install git and ansicolor plugins by default.
  jenkins::plugin { 'git-client':
    user => $jenkins_user,
    require => Package['git-core']
  }

  jenkins::plugin { 'git':
    user => $jenkins_user,
    require => Jenkins::Plugin['git-client']
  }

  jenkins::plugin { 'ansicolor':
    user => $jenkins_user,
  }
}
