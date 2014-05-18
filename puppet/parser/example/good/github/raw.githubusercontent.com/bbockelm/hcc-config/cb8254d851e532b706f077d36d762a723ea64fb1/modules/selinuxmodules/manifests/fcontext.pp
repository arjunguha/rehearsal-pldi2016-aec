class selinuxmodules::fcontext ( $context = "", $pathname = "", $policy = "targeted" ) {
    if ( $context == "" ) or ( $pathname == "" ) {
        fail("context and pathname must not be empty")
    }

    # This package provides semanage ???? NO IT DOESN'T
#    package {
#       policycoreutils-python:
#          name   => "policycoreutils-python",
#          ensure => present,
#    }

    package {
       policycoreutils:
          name   => "policycoreutils",
          ensure => present,
    }
    exec { "add_${context}_${pathname}":
        command => "semanage fcontext -a -t ${context} \"${pathname}\"",
        unless => "semanage fcontext -l|grep \"^${pathname}.*:${context}:\"",
#        require => Package['policycoreutils-python'],  ####-python um, what?  Nope.
        require => Package['policycoreutils'],
    }
}
