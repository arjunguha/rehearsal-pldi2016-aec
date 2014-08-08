# Class: openssh
#
# Manages openssh service 
#
# Usage:
# include openssh
# 
# Variables:
#
class openssh {

    # Load the variables used in this module. Check the params.pp file
    require openssh::params

    # Reassigns variables names for use in templates


    # Basic Package 
    package { "openssh":
        name   => "${openssh::params::packagename}",
        ensure => present,
    }
    
    service { "openssh":
        name       => "${openssh::params::servicename}",
        ensure     => running,
        enable     => true,
        hasrestart => true,
        hasstatus  => "${openssh::params::hasstatus}",
        require    => Package["openssh"],
    }

    file { "sshd_config":
        path    => "${openssh::params::configfile}",
        mode    => "${openssh::params::configfile_mode}",
        owner   => "${openssh::params::configfile_owner}",
        group   => "${openssh::params::configfile_group}",
        require => Package["openssh"],
        notify  => Service["openssh"],
        content => template("openssh/sshd_config.erb"),
        ensure  => present,
    }

    file { "openssh-init":
        path    => "${openssh::params::initconfigfile}",
        mode    => "${openssh::params::configfile_mode}",
        owner   => "${openssh::params::configfile_owner}",
        group   => "${openssh::params::configfile_group}",
        require => Package["openssh"],
        ensure  => present,
    }

    ssh_authorized_key { "red-man":
		ensure => "present",
		type => "ssh-rsa",
		key => "AAAAB3NzaC1yc2EAAAABIwAAAQEA3n0Auikb9DBXnMB1z+K1fym59ppEMVB+jvR86kdoyW4GMsnjp0u0MbC29ycCOvPuNg35DSKLNy0SAzBbyuH8ZxfxxTgYtQVeidgTqP0Ot2hac++Iz48/6Yyc8R+qaq6FTuxkeJmPT4wtA1ZjtT5MOZkepYMSCIyM6r4Ey8diTlqpHkqMfHGu9KFJMnux0tqEbZmI2KNXcujbcQ5FBbgZe4YnKFDk3bPnGqxpAgb6FrwUHL4BgVvJlOE2E04i7Zo9M+fB+dHvf1XzJIJ5weoVDUxVUBmEUpOhwdJwBuvCk9R2Ltsga5Jioeau9SgNYZd9uVNr5FY/omAwq2QMVaQPdQ==",
#		options => 'from="red-man.unl.edu,172.16.200.1"',
		user => "root",
    }

    ssh_authorized_key { "red-man-new":
		ensure => "present",
		type => "ssh-rsa",
      key => "AAAAB3NzaC1yc2EAAAABIwAAAQEAxgS/e4Fng+nVXFfI7LPfQ+sR9oyDXG4xvOC8a6YGJW9XdDVrCCGiDO/XZFs9+6nW8N1w7rPQpGmtj1L0NM6m07cJXvnXclC4eu99JliLlR6C6NH/efbWrfRYekKHwf6D8txBhcOWlZk8aQFgQipF9sYVqD64WUkdrcnK+iuvACopjiT+jgNETiXeJoIt92VtKHIcANfO8J9sXwK2XaU87PhjQxWi7z+P1AMMieNwA7MkohOSGW6L0NmVWeaazXTLvkY9kTcfQv3bvBnvjBI4iksJC1vFfg3mupehSoqEkduZQqyE1WfvhoI8SODydsFzrJpb4oNJWrE9Q+dw9EePFw==",
		user => "root",
    }

    ssh_authorized_key { "red-tape":
		ensure => "present",
		type => "ssh-rsa",
      key => "AAAAB3NzaC1yc2EAAAADAQABAAABAQDH3Leng9UsuhuIUs0rAPD7jPYlWmEsLGu9ZGKPM9a+3LLOqwKGxbF6nCl7FgaTJbkS03iGn7iLfB44nhrzHMCRlLPDW9cAJJheMfQJ5b/7xJgGcBci6AuOXu1euhPXesxOtEcN7dYC9k/obhh4suBtxnkRf8s5K8uJpecbuLdlOaTQTdtTIte65qm4lnQDwKSZiDQKQ9XVUUOpIois/FFW96w14AtgQHq5Mqy1RImRMfLopWh2Vrw9/lyby/SAQJ5jttxV1vZq12rOacOVrRmTka70cgj3D89wmMEgeLA9BJYqRWDj82AckD+YgEymTBzwZ/wNpus1dJ49qxypMHmd",
		user => "root",
    }

    ssh_authorized_key { "root@redtro.red.hcc.unl.edu":
		ensure => "present",
		type => "ssh-rsa",
      key => "AAAAB3NzaC1yc2EAAAADAQABAAABAQC8HHX5UzHWEWRp+gDp/vPstyAK64UmSMHpzemgBYIbFJXLSJtHEGd3aQ35gSpfhIJxUGj/kqNAG+2mrOdJlIBZBvgT4rD0Me3gyr1GUcZYKlCfe+uNjCbVXO0qageoZ/wgbsJsLqRw+cf8JmnUPu0ttGZA+zEAn3iTdVldTOqd7/b8JYCMV6oMMxkbE0BVyQqT5y5ZHX+7wqBMeljUJtCoxTuT5/trAc/8+eYqKfIC8HuLcevHR86CamNFy9yb2n7GsbQEM4/VJmlnexoaWjPW9iydsm9ImRYi8R8hGZk0bY8NI1nRIKN/uOlnQgliGQghecHki0Tiygjd0xVs598L",
		user => "root",
    }

    if $puppi == "yes" { include openssh::puppi }
    if $backup == "yes" { include openssh::backup }
    if $monitor == "yes" { include openssh::monitor }
    if $firewall == "yes" { include openssh::firewall }

    case $operatingsystem {
        default: { }
    }

    # Include project specific class if $my_project is set
    # The extra project class is by default looked in openssh module 
    # If $my_project_onmodule == yes it's looked in your project module
    if $my_project { 
        case $my_project_onmodule {
            yes,true: { include "${my_project}::openssh" }
            default: { include "openssh::${my_project}" }
        }
    }

    # Include debug class is debugging is enabled ($debug=yes)
    if ( $debug == "yes" ) or ( $debug == true ) { include openssh::debug }

}
