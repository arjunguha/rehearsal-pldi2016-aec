# This resource installs default dependencies for an instance, don't use it directly.
#
# === Authors
#
# Sander Bilo <sander@proteon.nl>
#
# === Copyright
#
# Copyright 2013 Proteon.
#
define liferay::instance::dependencies ($instance = $name, $version) {
  Tomcat::Lib::Maven {
    instance => $instance, }

  if versioncmp($version, '6.1') >= 0 {
    tomcat::lib::maven { "${instance}:support-tomcat-${version}":
      lib        => "support-tomcat.jar",
      instance   => $instance,
      groupid    => 'com.liferay.portal',
      artifactid => 'support-tomcat',
      version    => $version,
    }

    tomcat::lib::maven { "${instance}:portal-service-${version}":
      lib        => 'portal-service.jar',
      instance   => $instance,
      groupid    => 'com.liferay.portal',
      artifactid => 'portal-service',
      version    => $version,
    }
  } else {
    # TODO: This will break an upgrade process
    maven { "${::tomcat::params::home}/${instance}/tomcat/lib/portal-service.jar":
      groupid    => 'com.liferay.portal',
      artifactid => 'portal-service',
      version    => $version,
      packaging  => 'jar',
    }

    file { "${::tomcat::params::home}/${instance}/tomcat/lib/support-tomcat.jar": ensure => absent, }
  }

  tomcat::lib::maven { "${instance}:activation-1.1.1":
    lib        => 'activation.jar',
    groupid    => 'javax.activation',
    artifactid => 'activation',
    version    => '1.1.1',
  }

  tomcat::lib::maven { "${instance}:ccpp-1.0":
    lib        => 'ccpp.jar',
    groupid    => 'javax.ccpp',
    artifactid => 'ccpp',
    version    => '1.0',
  }

  tomcat::lib::maven { "${instance}:jms-1.1-rev-1":
    lib        => 'jms.jar',
    groupid    => 'javax.jms',
    artifactid => 'jms-api',
    version    => '1.1-rev-1',
  }

  tomcat::lib::maven { "${instance}:jta-1.1":
    lib        => 'jta.jar',
    groupid    => 'javax.transaction',
    artifactid => 'jta',
    version    => '1.1',
  }

  tomcat::lib::maven { "${instance}:jtds-1.3.0":
    lib        => 'jtds.jar',
    groupid    => 'net.sourceforge.jtds',
    artifactid => 'jtds',
    version    => '1.3.0',
  }

  tomcat::lib::maven { "${instance}:jutf7-1.0.0":
    lib        => 'jutf7.jar',
    groupid    => 'com.beetstra.jutf7',
    artifactid => 'jutf7',
    version    => '1.0.0',
  }

  tomcat::lib::maven { "${instance}:mail-1.4.7":
    lib        => 'mail.jar',
    groupid    => 'javax.mail',
    artifactid => 'mail',
    version    => '1.4.7',
  }

  tomcat::lib::maven { "${instance}:javax.persistence-2.0.0":
    lib        => 'persistence.jar',
    groupid    => 'org.eclipse.persistence',
    artifactid => 'javax.persistence',
    version    => '2.0.0',
  }

  tomcat::lib::maven { "${instance}:portlet-api-2.0":
    lib        => 'portlet-api.jar',
    groupid    => 'javax.portlet',
    artifactid => 'portlet-api',
    version    => '2.0',
  }
}
