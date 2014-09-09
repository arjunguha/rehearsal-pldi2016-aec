
node default {
  file {
    "/var/lib/jenkins/jobs" :
      owner   => jenkins,
      group   => nogroup,
      ensure  => directory,
      require => Class['jenkins::package'];

    # It still pains me dearly to have to do this dumb shit for the Git pugin
    "/var/lib/jenkins/.gitconfig" :
      owner    => jenkins,
      group    => nogroup,
      ensure   => file,
      content  => "[user]
  name  = Jenkins
  email = jenkins@localhost
";
  }

  # NOTE: This is a workaround for the 'jenkins' user getting created by the
  # debian package with a home directory of /home/jenkins. (LOLWUT)
  user {
    'jenkins' :
      home    => '/var/lib/jenkins',
      require => Class['jenkins::package'];
  }

  group {
    'puppet' :
      ensure => present;
  }

  case $operatingsystem {
    'opensuse' : {
      package {
        'git' :
          alias  => 'git',
          ensure => present;
        'ruby' :
          ensure => present;
        'rubygems' :
          ensure => present;
        'rubygem-rake' :
          ensure => present;
      }
    }
    default : {
      package {
        'git-core' :
          alias  => 'git',
          ensure => present;
        'ruby1.9' :
          ensure => present;
        'rubygems1.9' :
          ensure => present;
        'rcov' :
          ensure => present;
        'rake' :
          ensure => present;
      }
    }
  }

  class {
    'jenkins' :
      require => Package['git'];
    'demojobs': ;
    'democonfig' : ;
  }

  jenkins::plugin {
    # Source Control
    'git' : ;

    # Workflow
    'promoted-builds' : ;
    'claim' : ;
    'scriptler' : ;
    'managed-scripts' : ;

    # Running jobs
    'join' : ;
    'pathignore' : ;
    'cobertura' : ;
    'build-timeout' : ;
    'warnings' : ;
    'violations' : ;

    # Just for fun
    'beer' : ;

    # Display plugins
    'ansicolor' : ;
    'radiatorviewplugin' : ;
    'xfpanel' : ;
    'statusmonitor' : ;
  }
}
