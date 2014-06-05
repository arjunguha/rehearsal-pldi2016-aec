class php::tools::qatools {
    exec {
        "install-qa-tools":
            command => "pear install pear.phpqatools.org/phpqatools",
            require => Exec['pear-autodiscover'],
            creates => "/usr/bin/phpmd"
    }
}