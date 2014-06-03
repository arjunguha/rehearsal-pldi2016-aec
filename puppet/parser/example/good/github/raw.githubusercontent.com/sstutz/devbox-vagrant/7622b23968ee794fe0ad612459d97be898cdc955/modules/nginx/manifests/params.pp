class nginx::params (
) {
    case $::osfamily {
        'RedHat': {
            $pkg_name   = 'nginx'
            $svc_name   = 'nginx'
            $extensions = []
        }
        'Debian': {
            $pkg_name   = 'nginx'
            $svc_name   = 'nginx'
            $extensions = [
                'nginx-common',
                'nginx-full',
            ]
        }
        default: {
            fail("unknown osfamily: $::osfamily")
        }
    }
}