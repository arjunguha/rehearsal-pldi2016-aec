class base_packages {
  package { 'build-essential': ensure => present }
  package { 'git-core':        ensure => present }
  package { 'curl':            ensure => present }
  package { 'emacs':           ensure => present }
  package { 'imagemagick':     ensure => present }
}
