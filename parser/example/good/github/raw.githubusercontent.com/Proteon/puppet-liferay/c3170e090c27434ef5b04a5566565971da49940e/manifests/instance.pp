# == Resource: liferay::instance
#
# Note: the first time the instance is created, if you use the (default) JNDI connection,
# and version 6.1.1, some error messages will be displayed in the log.
# This is a known bug: http://issues.liferay.com/browse/LPS-29672
#
# === Parameters
#
# [*instance*]  The instance this liferay should be installed in (see tomcat::instance). This instance will be created if not
# defined separatly.
# [*version*]   The version of liferay to install (maven artifact version).
# [*jndi_database*] The jndi datasource used by the instance (defaults to 'jdbc/LiferayPool').
#
# === Variables
#
# === Examples
#
# This will install liferay 6.1.1 in a tomcat instance called liferay_com.
# liferay::instance { 'liferay_com':
#   version     => '6.1.1',
#}
#
# This will install the latest available Liferay CE in a tomcat instance called tomcat_1.
# liferay::instance { 'liferay_com':
#   instance    => 'tomcat_1',
#   version     => 'LATEST',
#}
#
# === Authors
#
# Sander Bilo <sander@proteon.nl>
#
# === Copyright
#
# Copyright 2013 Proteon.
#
define liferay::instance ($version, $use_hsql = false, $instance = $name, $jndi_database = 'jdbc/LiferayPool',) {
  include java
  include tomcat

  if ($version >= '6.2.0') {
    $java_version = 'oracle_1_7_0'
  } else {
    $java_version = 'oracle_1_6_0'
  }

  liferay::instance::properties { $name: }

  liferay::instance::dependencies { $name: version => $version, }

  Liferay::Property {
    instance => $instance, }

  if (!defined(Tomcat::Instance[$instance])) {
    tomcat::instance { $instance: java_version => $java_version }
  }

  liferay::property { "${instance}:jdbc.default.jndi.name":
    key   => 'jdbc.default.jndi.name',
    value => $jndi_database,
  }

  # Optionally use a hsql database, not recommended for production
  if ($use_hsql) {
    tomcat::jndi::database::hsql { "${instance}-${jndi_database}":
      resource_name => $jndi_database,
      instance      => $instance,
      url           => 'jdbc:hsqldb:data/hsql/lportal',
    }
  }

  # Before 6.1 deploying with maven isn't really working to great
  if versioncmp($version, '6.1') >= 0 {
    tomcat::webapp::maven { "${instance}:ROOT":
      webapp     => 'ROOT',
      instance   => $instance,
      groupid    => 'com.liferay.portal',
      artifactid => 'portal-web',
      version    => $version,
    }
  } else {
    # just nick from sourceforge?
    $webapp_filename = "liferay-portal-${version}.war"
    $webapp_url = "http://downloads.sourceforge.net/project/lportal/Liferay%20Portal/${version}/${webapp_filename}"

    exec { "Fetch liferay-portal-${version}.war for ${name}":
      command => "/usr/bin/wget -O /usr/share/java/${webapp_filename} ${webapp_url}",
      creates => "/usr/share/java/${webapp_filename}",
      require => Class['tomcat'],
    }

    file { "${::tomcat::params::home}/${instance}/tomcat/webapps/ROOT.war":
      ensure  => 'link',
      target  => "/usr/share/java/${webapp_filename}",
      force   => true,
      require => Exec["Fetch liferay-portal-${version}.war for ${name}"],
      before  => Tomcat::Service[$instance],
    }
  }

  file { "${tomcat::params::home}/${instance}/deploy":
    ensure => directory,
    owner  => $instance,
    group  => $instance,
  }

  file { "${tomcat::params::home}/${instance}/logs":
    ensure => directory,
    owner  => $instance,
    group  => $instance,
  }
}
