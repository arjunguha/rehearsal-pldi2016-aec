# Class: tomcat::sunjdk
#
#   Jeff McCune <jeff@puppetlabs.com>
#   2010-08-05
#
#   This class models the Sun Java Development Kit in Puppet
#
#   Developed and tested on CentOS 5.5 i386 and x86_64
#   NOTE: It is difficult to uninstall the JDK.  Take a snapshot
#   before evaluating this class.
#
#   NOTE: JJM I recommend services requiring Java establish a relationship
#   with the Class["tomcat::sunjdk"] using a parameter to allow different
#   java runtime classes.
#
# Parameters:
#
# Actions:
#
#   Installs the Sun Java Development Kit and Java Runtime
#   /usr/bin/java
#
# Requires:
#
# Sample Usage:
#
#   include tomcat::sunjdk
#
class tomcat::sunjdk {
  $module    = "tomcat"
  $class     = "${module}::sunjdk"
  $prefix    = "/etc/puppet/modules"
  $p1        = "${prefix}/${module}/files"
  $p2        = "puppet:///modules/${module}"
# Translate system architecture facts into strings used within java.
  $architecture_real = $architecture ? {
    "x86_64" => "x64",
		"i386"   => "i586",
    default  => $architecture,
  }
  $installer = "jdk-6u21-linux-${architecture_real}-rpm.bin"

	File { owner => "0", group => "0", mode  => "0644" }
  Exec { path => "/usr/kerberos/sbin:/usr/kerberos/bin:/usr/local/sbin:/usr/local/bin:/sbin:/bin:/usr/sbin:/usr/bin:/root/bin" }

  file {
    "/var/tmp/${installer}":
		  mode   => "0755",
		  source => [ "${p1}/${installer}", "${p2}/${installer}" ],
		  notify => Exec["install-jdk"],
  }
# JJM Note, this installation is difficult to undo do to the nature of the Sun
# installer script.  It does not use the system packaging system, so removal
# is difficult and tedious.
# Snapshots are recommended for rollback if running in a Virtual Machine.
  exec {
		"install-jdk":
      command => "/var/tmp/${installer} -noregister",
      cwd     => "/var/tmp",
      creates => "/usr/java",
  }
# Provide an anchor for resource relationships
	file {
    "/usr/java":
		  require => Exec["install-jdk"],
		  ensure  => "directory";
	}
}
# JJM EOF
