# == Definition: reprepro::distribution
#
# Adds a "Distribution" to manage.
#
# Parameters:
# - *name*: the name of the distribution
# - *ensure* present/absent, defaults to present
# - *repository*: the name of the distribution
# - *origin*: package origin
# - *label*: package label
# - *suite*: package suite
# - *architectures*: available architectures
# - *components*: available components
# - *description*: a short description
# - *sign_with*: email of the gpg key
# - *deb_indices*: file name and compression
# - *dsc_indices*: file name and compression
# - *update*: update policy name
# - *uploaders*: who is allowed to upload packages
# - *not_automatic*: automatic pined to 1 by using NotAutomatic,
#   value are "yes" or "no"
#
# Requires:
# - Class['reprepro']
#
# Example usage:
#
#   reprepro::distribution {'lenny':
#     ensure        => present,
#     repository    => 'my-repository',
#     origin        => 'Camptocamp',
#     label         => 'Camptocamp',
#     suite         => 'stable',
#     architectures => 'i386 amd64 source',
#     components    => 'main contrib non-free',
#     description   => 'A simple example of repository distribution',
#     sign_with     => 'packages@camptocamp.com',
#   }
#
define reprepro::distribution (
  $codename,
  $repository,
  $origin,
  $label,
  $suite,
  $architectures,
  $components,
  $description,
  $sign_with,
  $ensure=present,
  $deb_indices='Packages Release .gz .bz2',
  $dsc_indices='Sources Release .gz .bz2',
  $update='',
  $uploaders='',
  $fakecomponentprefix='',
  $not_automatic='yes'
) {

  include reprepro::params

  $notify = $ensure ? {
    'present' => Exec["export distribution ${name}"],
    default   => undef,
  }

  concat::fragment {"distibution-${name}":
    ensure  => $ensure,
    target  => "${reprepro::params::basedir}/${repository}/conf/distributions",
    content => template('reprepro/distribution.erb'),
    notify  => $notify,
  }

  # FIXME: this exec don't works with user=>reprepro ?!?
  exec {"export distribution ${name}":
    command     => "su -c 'reprepro -b ${reprepro::params::basedir}/${repository} export ${codename}' reprepro",
    refreshonly => true,
    require     => [User[reprepro], Reprepro::Repository[$repository]],
  }
}
