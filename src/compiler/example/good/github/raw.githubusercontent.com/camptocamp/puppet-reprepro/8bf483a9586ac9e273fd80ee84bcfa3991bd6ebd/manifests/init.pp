class reprepro {

  case $::osfamily {
    'Debian': { include reprepro::debian }
    default:  { notice "Unsupported osfamily ${::osfamily}" }
  }

}
