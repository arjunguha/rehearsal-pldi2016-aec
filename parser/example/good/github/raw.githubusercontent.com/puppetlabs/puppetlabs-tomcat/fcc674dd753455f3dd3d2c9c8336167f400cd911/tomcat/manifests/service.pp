# Class: tomcat::service
#
#   Jeff McCune <jeff@puppetlabs.com>
#   2010-08-13
#
#   This class models the tomcat service itself.
#
#   It requires class { "tomcat" } and is not present
#   within that class because web applications should
#   also establish a "require" relationship with class
#   tomcat and then notify the service.
#
#   This organization is a common pattern in puppet.
#
# Parameters:
#
# Actions:
#
#   Manage the tomcat service
#
# Requires:
#
#   Class["tomcat"]
#   Class["${java_runtime_class}"]
#
# Sample Usage:
#
#   include tomcat
#   include tomcat::sunjdk
#   include tomcat::service
#
class tomcat::service {
  $module = "tomcat"
# If another class manages the sun java runtime, change this variable.
  $java_runtime_class = "${module}::sunjdk"
  $class  = "${module}::service"
# JJM Look for files on the node filesystem first.
  $p1 = "${prefix}/${module}/files"
# JJM Look for files on the puppetmaster second.
  $p2 = "puppet:///modules/${module}"
# Resource defaults.
  File { owner => "0", group => "0", mode  => "0644" }
  Exec { path => "/usr/kerberos/sbin:/usr/kerberos/bin:/usr/local/sbin:/usr/local/bin:/sbin:/bin:/usr/sbin:/usr/bin:/root/bin" }
  service {
    "tomcat":
      require   => [ Class["${java_runtime_class}"], Class["${module}"] ],
      hasstatus => true,
      ensure    => running,
      enable    => true;
  }
  file {
    "/usr/bin/tomcat-check-script":
      mode    => "0755",
      source  => [ "${p1}/tomcat-check-script", "${p2}/tomcat-check-script" ],
      require => Service["tomcat"];
  }
  exec {
    "tomcat-check-script":
      command => "/usr/bin/tomcat-check-script",
      unless  => "/usr/sbin/lsof -n -i :8080",
      require => File["/usr/bin/tomcat-check-script"];
  }
}
