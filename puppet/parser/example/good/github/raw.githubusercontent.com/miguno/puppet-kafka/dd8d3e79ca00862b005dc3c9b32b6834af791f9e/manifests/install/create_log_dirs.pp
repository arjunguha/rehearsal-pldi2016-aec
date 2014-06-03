# == Define kafka::install::create_log_dirs
#
# A kind of helper "function" that recursively creates an array of directories.
#
# We need such a crude workaround because Puppet does not provide such a feature out of the box in a clean way.
#
# Usage: kafka::install::create_log_dirs { $array_of_dirs: }
#
# === Parameters
# We use the name (via $name) of the defined type to specify the input.  The input is expected to be an array of
# strings, where each string represents the absolute path of a directory.
#
# Example input: ['/foo/alice', '/foo/bob', '/bar']
#
# Note on Puppet behavior: $name is the variable used when iterating through this input array.
#
define kafka::install::create_log_dirs {
  # This exec ensures we create intermediate directories for directory with the full path $name
  exec { "create-kafka-log-directory-${name}":
    command => "mkdir -p ${name}",
    path    => ['/bin', '/sbin'],
  }
  ->
  file { "kafka-log-directory-${name}":
    ensure       => directory,
    path         => $name,
    owner        => $kafka::user,
    group        => $kafka::group,
    mode         => '0750',
    recurse      => true,
    recurselimit => 0,
  }
}
