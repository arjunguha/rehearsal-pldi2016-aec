class drupal::defaultsite {
  drupal::site { 'default':
    ensure         => present,
    admin_password => $drupal::admin_password,
    database       => $drupal::database,
    dbuser         => $drupal::dbuser,
    dbpassword     => $drupal::dbpassword,
    dbhost         => $drupal::dbhost,
    dbport         => $drupal::dbport,
    dbdriver       => $drupal::dbdriver,
    dbprefix       => $drupal::dbprefix,
    update         => $drupal::update,
    docroot        => $drupal::docroot,
    writeaccess    => $drupal::writeaccess,
    managedatabase => $drupal::managedatabase,
    managevhost    => $drupal::managevhost,
  }
}
