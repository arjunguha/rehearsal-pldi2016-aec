# necessary defaults
Exec {
  path => [
    '/usr/local/bin',
    '/opt/local/bin',
    '/usr/bin', 
    '/usr/sbin', 
    '/bin',
    '/sbin'],
  logoutput => true,
}

exec {"apt-update":
    command => "/usr/bin/apt-get update",
}

# execute apt-get update each time a package is downlorded
Exec["apt-update"] -> Package <| |>

#######################################################################
##  Nodes  ############################################################
#######################################################################

node default
{

    # install apache
    include apache
  
    # install augeas  
    include augeas

    # install php
    include php
    include php::apache

    # install mysql
    include mysql::server
    
    # install apc
    include apc
    
    # install xdebug
    include xdebug
    
    # install sqlite
    include sqlite
    
    # add user vagrant to group www-data
    user { "vagrant":
        groups => "www-data",
    }
    
}