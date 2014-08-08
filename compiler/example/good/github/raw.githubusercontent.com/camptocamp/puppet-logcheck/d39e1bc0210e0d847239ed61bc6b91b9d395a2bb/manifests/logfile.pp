define logcheck::logfile (
  $ensure=present,
  $file,
) {
  concat::fragment {$name:
    ensure  => $ensure,
    target  => '/etc/logcheck/logcheck.logfiles',
    content => "${file}\n",
  }
}
