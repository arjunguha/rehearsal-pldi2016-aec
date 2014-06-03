class pe_shared_ca::update_module inherits pe_shared_ca::params {
  $module_path = module_path($module_name)

  file { [
    "${module_path}/files",
    "${module_path}/files/ssl",
    "${module_path}/files/ssl/ca",
    "${module_path}/files/ssl/certs",
    "${module_path}/files/ssl/private_keys",
    "${module_path}/files/ssl/public_keys",
  ]:
    ensure => directory,
  }

  ## Copy files into module
  file { "${module_path}/files/credentials":
    ensure => file,
    source => '/etc/puppetlabs/mcollective/credentials',
  }
  #wrapper for ca files array
  pe_shared_ca::update_module::copy { $ca_files_to_copy:
    sourcedir => '/etc/puppetlabs/puppet/ssl',
    targetdir => "${module_path}/files/ssl",
  }
}
