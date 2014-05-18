class git::params {
  $packagename = $::operatingsystem ? {
    default => 'git',
  }
}

# vim:sw=2:ts=2:expandtab
