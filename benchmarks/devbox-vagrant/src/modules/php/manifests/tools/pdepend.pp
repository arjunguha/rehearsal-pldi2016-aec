class php::tools::pdepend {
    exec {
        "discover-pdepend":
            command => "pear channel-discover pear.pdepend.org",
            require => Exec["pear-upgrade"],
            notify  => Exec["install-pdepend"];

        "install-pdepend":
            command => "pear.pdepend.org/PHP_Depend-beta",
            creates => "/usr/bin/pdepend",
            refreshonly => true;
    }
}
