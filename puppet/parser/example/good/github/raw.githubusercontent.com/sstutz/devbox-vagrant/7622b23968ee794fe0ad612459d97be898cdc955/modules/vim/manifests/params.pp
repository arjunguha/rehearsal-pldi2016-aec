class vim::params
{
    case $::osfamily {
        'RedHat': {
            $pkg_name   = 'vim'
        }
        'Debian': {
            $pkg_name   = 'vim'
        }
        default: {
            fail("unknown osfamily: $::osfamily")
        }
    }
}