# Class: tomcat
#
#   Jeff McCune <jeff@puppetlabs.com>
#   2010-08-05
#   Status: This class is working and properly starts the tomcat service.
#
#   This class models the tomcat service in Puppet
#   Developed and tested on CentOS 5.5 x86_64
#
#   Once the service is running, connect to:
#   http://<ipaddress>:8080/
#
#   Don't forget to manage the system firewall.
#
#   A tomcat init script is also provided which uses the CATALINA_PID
#   environment variable exported by tomcat to check the service status.
#
#   For speed, this module will copy files from a local copy of this module
#   if present in /etc/puppet/modules/tomcat on the node.  If not present,
#   the module will download files from the puppet master.
#
# Parameters:
#
# Actions:
#
#   Unpacks tomcat into /usr/apache-tomcat-<version>
#   Links /usr/tomcat to /usr/apache/tomcat-<version>
#   Manages the tomcat service using the system service manager
#
# Requires:
#
#   Java Runtime.  Available in class tomcat::sunjdk within this module
#   If another java runtime is to be used, modify the $java_runtime_class
#   variable at the top of the tomcat class model.
#
#   Class["${java_runtime_class}"] provided by class { "tomcat::sunjdk": }
#
# Sample Usage:
#
#   include tomcat::sunjdk
#   include tomcat
#
class tomcat {
  $module = "tomcat"
  $prefix = "/etc/puppet/modules"
# JJM Look for files on the node filesystem first.
  $p1 = "${prefix}/${module}/files"
# JJM Look for files on the puppetmaster second.
  $p2 = "puppet:///modules/${module}"
# Our installer media.
  $tomcat_version = "5.5.30"
  $installer = "apache-tomcat-${tomcat_version}.tar.gz"
# Resource defaults.
  File { owner => "0", group => "0", mode  => "0644" }
  Exec { path => "/usr/kerberos/sbin:/usr/kerberos/bin:/usr/local/sbin:/usr/local/bin:/sbin:/bin:/usr/sbin:/usr/bin:/root/bin" }
# Resource models.
# JJM The tomcat installation tarball.  Copy from local cache if available.
  file {
    "/var/tmp/${installer}":
      source  => [ "${p1}/${installer}", "${p2}/${installer}" ],
  }
  exec {
    "unpack-tomcat":
      command => "tar -C /usr -x -z -f /var/tmp/${installer}",
      creates => "/usr/apache-tomcat-${tomcat_version}",
      require => File["/var/tmp/${installer}"];
  }
  file {
    "/usr/tomcat":
      ensure  => "/usr/apache-tomcat-${tomcat_version}",
      require => Exec["unpack-tomcat"];
    "/etc/init.d/tomcat":
      mode    => "0755",
      source  => [ "${p1}/tomcat-init-script", "${p2}/tomcat-init-script" ],
      require => File["/usr/tomcat"];
  }
}
# JJM EOF
