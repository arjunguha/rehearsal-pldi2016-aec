define python::pip::install (
  $venv,
  $package = undef,
  $ensure = present,
  $owner  = undef,
  $group  = undef
) {
  $pkgspec = $package ? {
    undef => $name,
    default => $package,
  }
  # Match against whole line if we provide a given version:
  $grep_regex = $pkgspec ? {
    /==/    => "^${pkgspec}\$",
    default => "^${pkgspec}==",
  }

  Exec {
    user  => $owner,
    group => $group,
    cwd   => "/tmp",
  }

  if $ensure == 'present' {
    exec { "pip install $name":
      command => "$venv/bin/pip install $pkgspec",
      unless  => "$venv/bin/pip freeze | grep -e $grep_regex"
    }
  } elsif $ensure == 'latest' {
    exec { "pip install $name":
      command => "$venv/bin/pip install -U $pkgspec",
    }
  } else {
    exec { "pip install $name":
      command => "$venv/bin/pip uninstall $pkgspec",
      onlyif  => "$venv/bin/pip freeze | grep -e $grep_regex"
    }
  }
}
