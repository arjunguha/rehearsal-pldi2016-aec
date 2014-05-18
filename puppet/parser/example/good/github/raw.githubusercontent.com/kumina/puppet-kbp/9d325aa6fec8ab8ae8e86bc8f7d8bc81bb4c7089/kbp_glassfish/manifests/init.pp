# Author: Kumina bv <support@kumina.nl>

class kbp_glassfish {
  include gen_glassfish
  include kbp_munin::client::glassfish

  group { "glassfish":
    gid     => 2000,
    require => Package["glassfish"];
  }

  user { "glassfish":
    uid         => "2000",
    gid         => "glassfish",
    managehome  => false,
    require     => [Package["glassfish"], Group["glassfish"]]
  }

  setfacl {
    "Directory permissions on /srv/glassfish for user glassfish":
      dir     => "/srv/glassfish",
      acl     => "default:user:glassfish:rwx",
      require => File["/srv/glassfish"];
    "Directory permissions on /srv/glassfish for group glassfish":
      dir => "/srv/glassfish",
      acl => "default:group:glassfish:rwx",
      require => File["/srv/glassfish"];
  }

  file {
    ["/srv/glassfish","/srv/glassfish/domains"]:
      ensure  => directory,
      owner   => "glassfish",
      group   => "glassfish",
      mode    => 775,
      require => User["glassfish"];
    "/opt/glassfish/domains":
      ensure  => link,
      target  => "/srv/glassfish/domains",
      owner   => "glassfish",
      group   => "glassfish",
      force   => true,
      require => [File["/srv/glassfish/domains"],Package["glassfish"]];
  }

  # Patches to work around glassfish 3.1.2 http/ajp bugs
  # see http://java.net/jira/browse/GLASSFISH-18446
  kbp_glassfish::patch {
    ["grizzly-http.jar","grizzly-http-ajp.jar"]:;
  }
}

class kbp_glassfish::patch::jmx {
  # Patches to work around glassfish 3.1.2 JMX bugs
  # see http://java.net/jira/browse/GLASSFISH-18450
  kbp_glassfish::patch {
    ["container-common.jar", "glassfish-mbeanserver.jar", "internal-api.jar", "rest-service.jar"]:;
  }
}

class kbp_glassfish::cluster {
  include kbp_glassfish

  file {
    "/srv/glassfish/nodes":
      ensure  => directory,
      owner   => "glassfish",
      group   => "glassfish",
      mode    => 775,
      require => User["glassfish"];
    "/opt/glassfish/nodes":
      ensure  => link,
      target  => "/srv/glassfish/nodes",
      owner   => "glassfish",
      group   => "glassfish",
      mode    => 775,
      require => User["glassfish"];
  }
}

# Define: kbp_glassfish::domain
#
# Actions:
#  Undocumented
#
# Parameters:
#  portbase
#   The portbase value determines where the port assignment should start. See gen_glassfish::domain for more info
#  ensure
#   Either running or stopped (for now...)
#  autostart
#   Should this domain bestarted on boot and when invoking /etc/init.d/glassfish start
#  web_address
#   The address apache should bind on. Defaults to "*".
#  web_servername
#   Set this to the server name if you need an apache in front of this glassfish
#  web_serveralias
#   An array of server aliases
#  web_port
#   The port we should listen on (keep it at 80)
#  web_sslport
#   Either false or 443 (SSL not implemented yet in this define)
#  web_redundant
#   Is this domain redundant (i.e. is there another server with the same domain that is possibly behind the same loadbalancer)
#  XXX Rutger, dit is niet ge-implementeerd... is dit nodig?
#  java_monitoring
#   Should we monitor the JVM?
#  java_servicegroups
#   Which Icinga service groups will recieve alerts from the JVM monitoring
#  monitoring_sms
#   Should we send SMSes when there is something wrong with this domain?
#  monitoring_statuspath
#   Where can we find status.html
#  mbean_objectname
#
#  mbean_attributename
#
#  mbean_expectedvalue
#
#  mbean_attributekey
#
#
# Depends:
#  gen_puppet
#  gen_glassfish::domain
#
define kbp_glassfish::domain($portbase, $ensure="present", $jmx_port = false, $web_address = "*",
    $web_servername=false, $web_serveralias = [], $web_port = "80", $web_sslport = false, $web_redundant=false,
    $java_monitoring=false, $java_servicegroups=false, $monitoring_sms=true, $monitoring_statuspath=false,
    $mbean_objectname=false, $mbean_attributename=false, $mbean_expectedvalue=false, $mbean_attributekey=false) {

  if $jmx_port {
    $jmxport = $jmx_port
  } else {
    $jmxport = $portbase + 86
  }

  # Whether the domain should be auto started (the customer can put an 'autostart' file in the root of the domain/<name> directory
  $autostart = $name in split($glassfish_autostart_domains, ',')

  gen_glassfish::domain { $name:
    portbase  => $portbase,
    ensure    => $ensure ? {
      "present" => $autostart ? {
        true    => "running",
        default => "",
      },
      default => $ensure,
    };
  }

  # Override this require, as we want domains to be in /srv/glassfish/domains
  Exec <| title == "Create glassfish domain ${name}" |> {
    require => File["/srv/glassfish/domains"],
    creates => "/srv/glassfish/domains/${name}",
  }

  file { "/srv/glassfish/domains/${name}":
    ensure  => directory,
    owner   => "glassfish",
    group   => "glassfish",
    mode    => 755,
    require => Exec["Create glassfish domain ${name}"];
  }

  kbp_glassfish::instance { $name:
    portbase           => $portbase,
    java_monitoring    => $java_monitoring,
    sms                => $sms,
    java_servicegroups => $java_servicegroups;
  }

  if $web_servername { # We want an Apache in front of it.
    # Portbase +10 is unused.. let's use it as jk port.
    $jkport = $portbase + 10

    kaugeas { "JK listener for ${name}":
      file    => "/srv/glassfish/domains/${name}/config/domain.xml",
      lens    => "Xml.lns",
      changes => ["set domain/configs/config[#attribute/name = 'server-config']/network-config/network-listeners/network-listener[#attribute/name = 'jk-connector']/#attribute/name 'jk-connector'",
                  "set domain/configs/config[#attribute/name = 'server-config']/network-config/network-listeners/network-listener[#attribute/name = 'jk-connector']/#attribute/port '${jkport}'",
                  "set domain/configs/config[#attribute/name = 'server-config']/network-config/network-listeners/network-listener[#attribute/name = 'jk-connector']/#attribute/protocol 'jk-connector'",
                  "set domain/configs/config[#attribute/name = 'server-config']/network-config/network-listeners/network-listener[#attribute/name = 'jk-connector']/#attribute/transport 'tcp'",
                  "set domain/configs/config[#attribute/name = 'server-config']/network-config/network-listeners/network-listener[#attribute/name = 'jk-connector']/#attribute/thread-pool 'jk-connector'",
                  "set domain/configs/config[#attribute/name = 'server-config']/network-config/network-listeners/network-listener[#attribute/name = 'jk-connector']/#attribute/jk-enabled 'true'",
                  "set domain/configs/config[#attribute/name = 'server-config']/network-config/network-listeners/network-listener[#attribute/name = 'jk-connector']/#attribute/address '127.0.0.1'"
                 ],
     require => Exec["Create glassfish domain ${name}"];
    }

    kbp_glassfish::domain::site { $web_servername:
      webaddress       => $web_address,
      glassfish_domain => $name,
      jkport           => $jkport,
      webport          => $web_port,
      require          => Augeas["JK listener for ${name}"];
    }
  } else {
    kbp_icinga::mbean_value { $name:
      jmxport       => $jmxport,
      objectname    => $mbean_objectname,
      attributename => $mbean_attributename,
      expectedvalue => $mbean_expectedvalue,
      attributekey  => $mbean_attributekey ? {
        false   => undef,
        default => $mbean_attributekey,
      },
      customname    => "Glassfish ${name} status";
    }
  }

}

# Define: kbp_glassfish::domain::site
#
# Actions:
#  Setup an apache vhost for the glassfish_domain, use this in the customer-specific code when
#  we _don't_ create the domain/instance, but the client wants monitoring+trending.
#
# Parameters:
#  glassfish_domain:
#   Name of the domain (to connect to)
#  jkport:
#   The port to connect to
#  webaddress
#   The address Apache should listen to. Defaults to "*".
#  webport:
#   External port to listen on for HTTP traffic
#  TODO ssl options
#  statuspath:
#   a path to check om (e.g. /status.html)
#  access_logformat
#   The logformat that Apache should use.
#
define kbp_glassfish::domain::site ($glassfish_domain, $jkport, $webport=80, $statuspath=false, $ensure="present", $access_logformat="combined", $connector_loglevel="info", $serveralias=false, $webaddress="*", $monitoring_ha=false,
    $monitor_statuscode='200', $monitoring=true) {
  if ! $monitoring {
    $monitor = false
  } elsif $glassfish_domain in split($glassfish_autostart_instances, ',') {
    $monitor = true
  } else {
    $monitor = false
  }

  kbp_apache::site { $name:
    address            => $webaddress,
    serveralias        => $serveralias,
    access_logformat   => $access_logformat,
    ensure             => $ensure,
    ha                 => $monitoring_ha,
    monitor            => $monitor,
    monitor_statuscode => $monitor_statuscode;
  }

  kbp_apache::glassfish_domain { $glassfish_domain:
    site               => $name,
    port               => $webport,
    connector_loglevel => $connector_loglevel,
    connector_port     => $jkport;
  }
}

# Define: kbp_glassfish::instance
#
# Actions:
#  Setup monitoring and trending, use this in the customer-specific code when
#  we _don't_ create the domain/instance, but the client wants monitoring+trending.
#
# Parameters:
#  portbase:
#   The portbase for this instance
#  java_monitoring:
#   Do we want to monitor?
#  sms:
#   Do we (kumina) want to receive SMSes?
#  java_servicegroups:
#   which Icinga servicegroup should receive notifications?
#
define kbp_glassfish::instance ($portbase, $java_monitoring=true, $sms=true, $java_servicegroups=false, $jmx_port = false, $username=false, $password=false, $autostart_path=false){
  if $jmx_port {
    $jmxport = $jmx_port
  } else {
    $jmxport = $portbase+86
  }

  if $java_monitoring and $name in split($glassfish_autostart_instances, ',') {
    kbp_icinga::java { "${name}_${jmxport}":
      servicegroups  => $java_servicegroups ? {
        false   => undef,
        default => $java_servicegroups,
      },
      sms            => $sms,
      username       => $username,
      password       => $password,
      autostart_path => $autostart_path;
    }
  }

  kbp_munin::client::glassfish_instance { $name:
    jmxport => $jmxport,
    jmxuser => $username,
    jmxpass => $password;
  }

  file { "/etc/init.d/glassfish-instance-${name}" :
    content => template('kbp_glassfish/instance.init'),
    mode    => 770,
    notify  => Gen_insserv::Enable_script["glassfish-instance-${name}"],
    require => Package['glassfish'];
  }

  gen_insserv::enable_script { "glassfish-instance-${name}":; }
}

# Define: kbp_glassfish::patch
#
# Actions: Move a jar from /srv/glassfish/patches to $destdir
#
# Parameters
#  ensure:
#   Set to absent to remove the file (will not restore the original!)
#  destdir:
#   The directory the file should be placed in
#  location:
#   Where the file should be sourced from (puppet:///modules/${location}/${name}).
#
define kbp_glassfish::patch ($ensure = present, $destdir = "/opt/glassfish/modules", $location = 'kbp_glassfish/patches'){
  file { "${destdir}/${name}":
    ensure  => $ensure,
    source  => "puppet:///modules/${location}/${name}",
    owner   => "root",
    group   => "root",
    mode    => 644,
    require => Package["glassfish"];
  }
}
