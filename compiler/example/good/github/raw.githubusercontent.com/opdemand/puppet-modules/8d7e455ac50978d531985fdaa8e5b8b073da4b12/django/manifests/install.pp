class django::install {

  require django::params
  
  $packages = $django::params::database_type ? {
    postgresql => [ "python-django" , "python-psycopg2" ],
    # need to find the right driver package names
    mysql => [ "python-django" , "python-mysql" ],
    oracle => [ "python-django" , "python-oracle" ],
  }

  $database_service = "$django::params::database_type"

  if defined(Service[$database_service]) {
    $package_requires = Service["$database_service"]
  } else {
    $package_requires = []
  }  
  
  package { $packages:
      ensure => latest,
      require => $package_requires,
  }

}
