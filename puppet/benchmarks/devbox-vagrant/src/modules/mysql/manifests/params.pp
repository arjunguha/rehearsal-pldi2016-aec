class mysql::params {

    case $::osfamily {
        'RedHat': {
            $pkg_name   = ''
            $svc_name   = ''
        }
        'Debian': {
            $pkg_name   = 'mysql-server'
            $svc_name   = 'mysql'
        }
        default: {
            fail("unknown osfamily: $::osfamily")
        }
    }
}