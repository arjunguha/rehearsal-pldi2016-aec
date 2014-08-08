# vim: ts=2: sw=2
# Node definitions for the EXAMPLE1 environment

# puppet master
node echo inherits ex1_style_puppetmaster {
  include ex1_role_puppetmaster
}
# puppet slaves
node oreo inherits ex1_style_puppetslave {
  include ex1_role_puppetslave
}
node deimos inherits ex1_style_puppetslave {
  $my_puppet_version = '2.6.2-4'
  $my_passenger_version = '3.0.6'
  include ex1_role_puppetslave
}
