#
# Class: osg-ca-certs
#
# simple module for osg-ca-certs RPM distribution
# keeps it up to date and requires fetch-crl to ensure proper CRL updating
#
class osg-ca-certs {


	package { osg-ca-certs: name => "osg-ca-certs", ensure => latest }
	package { cilogon-ca-certs: name => "cilogon-ca-certs", ensure => latest }

	include fetch-crl

	file { "/etc/grid-security/certificates/hcc_puppet_ca.pem":
                ensure => present,
                owner  => "root", group => "root", mode => 755,
                source => "puppet:///modules/osg-ca-certs/ca_crt.pem",
        }
   file { "/etc/grid-security/certificates/hcc_puppet_crl.pem":
                ensure => present,
                owner  => "root", group => "root", mode => 755,
                source => "puppet:///modules/osg-ca-certs/ca_crl.pem",
        }
	file { "/etc/grid-security/certificates/c15bdab5.signing_policy":
                ensure => present,
                owner  => "root", group => "root", mode => 755,
                source => "puppet:///modules/osg-ca-certs/c15bdab5.signing_policy",
        }

	file { "/etc/grid-security/certificates/1592d59f.signing_policy":
                ensure => present,
                owner  => "root", group => "root", mode => 755,
                source => "puppet:///modules/osg-ca-certs/c15bdab5.signing_policy",
        }

	file { "/etc/grid-security/certificates/c15bdab5.0":
					 ensure => link,
					 target => "/etc/grid-security/certificates/hcc_puppet_ca.pem",
		  }
	
	file { "/etc/grid-security/certificates/1592d59f.0":
					 ensure => link,
					 target => "/etc/grid-security/certificates/hcc_puppet_ca.pem",
		  }

	file { "/etc/grid-security/certificates/1592d59f.r0":
					 ensure => link,
					 target => "/etc/grid-security/certificates/hcc_puppet_crl.pem",
		  }
	file { "/etc/grid-security/certificates/c15bdab5.r0":
                ensure => link,
                target => "/etc/grid-security/certificates/hcc_puppet_crl.pem",
        }

}


