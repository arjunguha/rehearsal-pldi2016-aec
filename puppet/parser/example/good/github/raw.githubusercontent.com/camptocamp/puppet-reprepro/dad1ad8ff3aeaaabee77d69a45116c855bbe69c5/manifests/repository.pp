# == Definition: reprepro::repository
#
# Adds a packages repository.
#
# Parameters:
# - *name*: the name of the repository
# - *ensure*: present/absent, defaults to present
# - *incoming_name*: the name of the rule-set, used as argument
# - *incoming_dir*: the name of the directory to scan for .changes files
# - *incoming_tmpdir*: directory where the files are copied into before
#   they are read
# - *incoming_allow*: allowed distributions
#
# Requires:
# - Class['reprepro']
#
# Example usage:
#
#   reprepro::distribution {'dev-lenny-backports':
#     ensure        => present,
#     repository    => 'dev',
#     codename      => 'lenny-backports',
#     origin        => 'Camptocamp',
#     label         => 'Camptocamp',
#     suite         => 'lenny-backports',
#     architectures => 'i386 amd64 source',
#     components    => 'main contrib non-free',
#     description   => 'Camptocamp consolidated lenny-backports dev-repository',
#     sign_with     => 'packages@mycompagny',
#     update        => 'lenny-backports',
#   }
#
define reprepro::repository (
  $ensure=present,
  $incoming_name='incoming',
  $incoming_dir='incoming',
  $incoming_tmpdir='tmp',
  $incoming_allow=''
  ) {

  include reprepro::params

  $file_ensure = $ensure ? {
    present => directory,
    default => $ensure,
  }

  $file_purge = $ensure ? {
    present => undef,
    default => true,
  }

  $file_recurse = $ensure ? {
    present => undef,
    default => true,
  }

  $file_force = $ensure ? {
    present => undef,
    default => true,
  }

  file {
    [
      "${reprepro::params::basedir}/${name}/conf",
      "${reprepro::params::basedir}/${name}/lists",
      "${reprepro::params::basedir}/${name}/db",
      "${reprepro::params::basedir}/${name}/logs",
      "${reprepro::params::basedir}/${name}/tmp",
    ]:
      ensure  => $file_ensure,
      purge   => $file_purge,
      recurse => $file_recurse,
      force   => $file_force,
      mode    => '2750',
      owner   => reprepro,
      group   => reprepro;

    [
      "${reprepro::params::basedir}/${name}",
      "${reprepro::params::basedir}/${name}/dists",
      "${reprepro::params::basedir}/${name}/pool",
    ]:
      ensure  => $file_ensure,
      purge   => $file_purge,
      recurse => $file_recurse,
      force   => $file_force,
      mode    => '2755',
      owner   => reprepro,
      group   => reprepro;

    "${reprepro::params::basedir}/${name}/incoming":
      ensure  => $file_ensure,
      purge   => $file_purge,
      recurse => $file_recurse,
      force   => $file_force,
      mode    => '2770',
      owner   => reprepro,
      group   => reprepro;

    "${reprepro::params::basedir}/${name}/conf/options":
      ensure  => $ensure,
      mode    => '0640',
      owner   => reprepro,
      group   => reprepro,
      content => "verbose\nask-passphrase\nbasedir .\n";

    "${reprepro::params::basedir}/${name}/conf/incoming":
      ensure  => $ensure,
      mode    => '0640',
      owner   => reprepro,
      group   => reprepro,
      content => template('reprepro/incoming.erb');
  }

  concat {"${reprepro::params::basedir}/${name}/conf/distributions":
    owner   => root,
    group   => root,
    mode    => '0644',
    force   => true,
    require => File["${reprepro::params::basedir}/${name}/conf"],
  }

  concat {"${reprepro::params::basedir}/${name}/conf/updates":
    owner   => root,
    group   => root,
    mode    => '0644',
    force   => true,
    require => File["${reprepro::params::basedir}/${name}/conf"],
  }

  # removed folders originally created by common::concatfilepart
  file {["${reprepro::params::basedir}/${name}/conf/distributions.d",
    "${reprepro::params::basedir}/${name}/conf/updates.d"]:
      ensure  => absent,
      purge   => true,
      recurse => true,
      force   => true,
  }

}
