define pe_shared_ca::update_module::copy (
  $sourcedir,
  $targetdir,
) {
  $filename = $name
  file { "${targetdir}/${filename}":
    source => "${sourcedir}/${filename}",
  }
}
