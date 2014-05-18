# Class puppet::red::server
#
# Custom project class for red project. Use this to adapt the puppet server settings to your project.
# This class is autoloaded if $my_module == red and $my_module_onmodule != yes
# If $my_module_onmodule == yes Puppet tries to autoload red::puppet::server
# that is:  MODULEPATH/red/manifests/puppet/server.pp
#
class puppet::red::server inherits puppet::server {

#    File["puppet.conf"] {
#        content => template("puppet/red/server/puppet.conf.erb"),
#    }

#    File["namespaceauth.conf"] {
#        content => template("puppet/red/server/namespaceauth.conf.erb"),
#    }

}
