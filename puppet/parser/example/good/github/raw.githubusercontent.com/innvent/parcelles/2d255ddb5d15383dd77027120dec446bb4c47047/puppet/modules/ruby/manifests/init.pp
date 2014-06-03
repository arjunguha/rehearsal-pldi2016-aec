class ruby (
  $user = "ubuntu",
  $version = "1.9.3-p448"
) {
  # YUI Compressor gem needs it

  # Common deps for ruby gems from most ruby projects.
  package { [ "imagemagick", "libmagickwand-dev", "libsqlite3-dev" ]:
    ensure => latest
  }
  require java

  rbenv::install { $user: }
  ->
  rbenv::compile { $version:
    user => $user,
    global => true
  }
}
