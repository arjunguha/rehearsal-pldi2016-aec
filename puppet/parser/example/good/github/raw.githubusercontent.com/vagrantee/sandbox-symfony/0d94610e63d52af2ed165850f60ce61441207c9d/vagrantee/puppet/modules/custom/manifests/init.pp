####################################################################################
#
# CUSTOM MANIFEST
#
# Add your custom procedures here
# this procedures will run after the server is provisioned.
#
####################################################################################

class custom() {

  /* console commands */
  symfony::console { 'doctrine:migrations:migrate': }

  symfony::console { 'doctrine:fixtures:load':
    require => Symfony::Console['doctrine:migrations:migrate'],
  }

  symfony::console { 'assetic:dump': }

}