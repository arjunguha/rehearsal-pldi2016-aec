class php::params (
) {
    case $::osfamily {
        'RedHat': {
            $pkg_name   = ''
            $svc_name   = ''
        }
        'Debian': {
            $pkg_name   = 'php5'
            $svc_name   = 'php5-fpm'
            $php_exts   = [
                'php5-memcached',
                'php5-memcache',
                'php5-imagick',
                'php5-mcrypt',
                'php5-curl',
                'php5-intl',
                'php-pear',
                'php5-xsl',
                'php5-cli',
                'php5-dev',
                'php5-gd',
                'php5-mysqlnd'
            ]
        }
        default: {
            fail("unknown osfamily: $::osfamily")
        }
    }
}
