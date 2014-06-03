#-----------------------------------------------------------------------------
#   Copyright (c) 2012 Bryce Johnson
#
#   Licensed under the Apache License, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   Unless required by applicable law or agreed to in writing, software
#   distributed under the License is distributed on an "AS IS" BASIS,
#   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#   See the License for the specific language governing permissions and
#   limitations under the License.
#-----------------------------------------------------------------------------
class stash::config {

  require stash::params

  file { "${stash::params::webappdir}/bin/setenv.sh":
    content => template('stash/setenv.sh.erb'),
    mode    => '0755',
    owner   => "${stash::params::user}",
    group   => "${stash::params::group}",
    require => [Class['stash::install'], Class['stash::user']],
  }

  exec { 'mkdirp-homedir-stash':
    cwd     => "${stash::params::tmpdir}",
    command => "/bin/mkdir -p ${stash::params::homedir}",
    creates => "${stash::params::homedir}",
  }

  file { "${stash::params::homedir}":
    ensure  => 'directory',
    owner   => "${stash::params::user}",
    group   => "${stash::params::group}",
    require => [Exec['mkdirp-homedir-stash'], Class['stash::user']],
  }

  file { "${stash::params::homedir}/stash-config.properties":
    content => template('stash/stash-config.properties.erb'),
    mode    => '0644',
    owner   => "${stash::params::user}",
    group   => "${stash::params::group}",
    require => [Class['stash::install'],Class['stash::user'],Exec["mkdirp-homedir-stash"]],
  }

  if "${stash::params::db}" == 'postgresql' {
    file { "${stash::params::homedir}/dbconfig.xml":
      content => template('stash/dbconfig.postgres.xml.erb'),
      mode    => '0600',
      owner   => "${stash::params::user}",
      group   => "${stash::params::group}",
      require => [Class['stash::install'],Exec['mkdirp-homedir-stash']],
      notify  => Class['stash::service'],
    }
  }
  if "${stash::params::db}" == 'mysql' {
    file { "${stash::params::homedir}/dbconfig.xml":
      content => template('stash/dbconfig.mysql.xml.erb'),
      mode    => '0600',
      owner   => "${stash::params::user}",
      group   => "${stash::params::group}",
      require => [Class['stash::install'],Exec['mkdirp-homedir-stash']],
      notify  => Class['stash::service'],
    }
  }
}