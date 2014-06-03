# Node definitions for the EXAMPLE2 environment
# vim: ts=2: sw=2
#

# puppet master
node sleepy inherits ex2_style_puppetmaster {
  include ex2_role_puppetmaster 
}
# puppet slaves
node handsome inherits ex2_style_puppetslave {
  include ex2_role_puppetslave
}
node evil inherits ex2_style_puppetslave {
  $my_puppet_version = '2.6.2-4'
  $my_passenger_version = '3.0.6'
  include ex2_role_puppetslave
}
