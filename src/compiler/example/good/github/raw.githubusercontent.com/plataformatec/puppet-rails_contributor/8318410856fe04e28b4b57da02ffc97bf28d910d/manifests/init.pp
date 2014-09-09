# Public: Configure a development environment to contribute to the Rails project
#
# Usage:
#
#   include rails_contributor
#   # or
#   class { 'rails_contributor': repositories => ['rails', 'arel'] }
class rails_contributor(
  $repositories = rails_repos(),
  $ruby_versions = ['1.9.3', '2.0.0', '2.1.1'],
) {
  include boxen::config

  $dir = "${boxen::config::srcdir}/rails"

  include postgresql
  include mysql
  ruby::version { $ruby_versions: }

  file { $dir:
    ensure => directory
  }

  rails_contributor::project { $repositories: }

  file { "${dir}/rails/activerecord/test/config.yml":
    ensure  => present,
    source  => 'puppet:///modules/rails_contributor/config.yml',
    require => Rails_Contributor::Project['rails']
  }
}
