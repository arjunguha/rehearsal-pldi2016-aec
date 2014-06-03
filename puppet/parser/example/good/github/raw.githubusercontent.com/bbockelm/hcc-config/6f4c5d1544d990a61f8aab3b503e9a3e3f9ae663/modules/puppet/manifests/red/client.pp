# Class puppet::red::client
#
# Custom project class for red project. Use this to adapt the puppet client settings to your project.
# This class is autoloaded if $my_module == red and $my_module_onmodule != yes
# If $my_module_onmodule == yes Puppet tries to autoload red::puppet::client
# that is:  MODULEPATH/red/manifests/puppet/client.pp
#
#
class puppet::red::client inherits puppet::client {

}

