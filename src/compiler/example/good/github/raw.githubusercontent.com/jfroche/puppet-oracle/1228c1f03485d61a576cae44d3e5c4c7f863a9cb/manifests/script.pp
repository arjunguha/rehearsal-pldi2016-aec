define oracle::script
(
  $db_user,
  $sql,
  $sysdba = false
)
{
  $db_pass = hiera("oracle_${db_user}_password")

  file {
    "/oracle/bin/$name":
      ensure  => present,
      owner   => oracle,
      group   => oracle,
      mode    => '0755',
      content => template('oracle/oraclescript'),
      require => File['/oracle/bin'],
  }
}