class php::tools::phpdoc {
    exec {
    	"discover-phpdoc-channel":
    		command => "pear channel-discover pear.phpdoc.org",
            unless  => "test -f /usr/bin/phpdoc",
            require => Exec["pear-upgrade"],
            notify  => Exec['install-phpdocumentor'];

        "install-phpdocumentor":
            command     => "pear install --alldeps phpdoc/phpDocumentor",
            timeout     => 0,
            refreshonly => true,
            creates 	=> "/usr/bin/phpdoc";
    }
}