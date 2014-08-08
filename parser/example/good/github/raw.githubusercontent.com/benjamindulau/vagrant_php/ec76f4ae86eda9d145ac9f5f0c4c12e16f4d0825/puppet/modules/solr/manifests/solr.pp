class solr::solr($version = '4.0.0') {
    exec { "solrDownload":
        cwd => "/var/tmp",
        command => "wget http://apache.mirrors.multidist.eu/lucene/solr/${version}/apache-solr-${version}.tgz",
		creates => "/var/tmp/apache-solr-${version}.tgz",
        path => ["/bin", "/usr/bin"],
		require => Package["tomcat6"],
        notify => Exec["solrExtract"],
    }

    exec { "solrExtract":
        cwd => "/var/tmp",
        command => "tar -xzf apache-solr-${version}.tgz",
        creates => "/var/tmp/apache-solr-${version}",
        path => ["/bin", "/usr/bin"],
        require => Exec["solrDownload"],
        notify => Exec["solrInstall"],
    }

	exec { "solrInstall":
		cwd => "/var/tmp",
		command => "cp apache-solr-${version}/dist/apache-solr-${version}.war /var/lib/tomcat6/webapps/solr.war",
		creates => "/var/lib/tomcat6/webapps/solr.war",
        path => ["/bin", "/usr/bin"],
		require => Exec["solrExtract"],
	}

	file { "/etc/solr":
		ensure => "directory",
	}

#	file { "solr_config":
#        path => "/etc/solr/solr.xml",
#		ensure => file,
#        owner => "root",
#        group => "root",
#        content => template("solr/solr_config.xml"),
#        require => [Exec["solrInstall"], File["/etc/solr"]],
#        notify => Service["tomcat6"],
#    }

	file { "solr_catalina":
        path => "/etc/tomcat6/Catalina/localhost/solr.xml",
        ensure => file,
        owner => "root",
        group => "root",
        content => template("solr/solr_catalina.xml"),
        require => [Exec["solrInstall"], File["/etc/solr"]],
        notify => Service["tomcat6"],
    }
}