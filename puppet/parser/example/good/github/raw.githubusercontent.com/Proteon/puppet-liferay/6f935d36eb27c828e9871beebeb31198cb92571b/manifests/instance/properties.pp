# This resource installs default properties for an instance, don't use it directly.
#
# === Authors
#
# Sander Bilo <sander@proteon.nl>
#
# === Copyright
#
# Copyright 2013 Proteon.
#
define liferay::instance::properties ($instance = $name) {
    include concat::setup

    concat { [
        "${tomcat::params::home}/${instance}/tomcat/lib/portal-ext.properties",
        "${tomcat::params::home}/${instance}/tomcat/lib/system-ext.properties",
        "${tomcat::params::home}/${instance}/tomcat/lib/portlet-ext.properties",]:
        owner => $instance,
        group => $instance,
        mode  => '0750',
        require => File["${tomcat::params::home}/${instance}/tomcat/lib"],
    }

    concat::fragment { "${instance} portal-ext.properties header":
        target  => "${tomcat::params::home}/${instance}/tomcat/lib/portal-ext.properties",
        order   => 00,
        content => "# Managed by puppet\n",
    }

    concat::fragment { "${instance} portlet-ext.properties header":
        target  => "${tomcat::params::home}/${instance}/tomcat/lib/portlet-ext.properties",
        order   => 00,
        content => "# Managed by puppet\n",
    }

    concat::fragment { "${instance} system-ext.properties header":
        target  => "${tomcat::params::home}/${instance}/tomcat/lib/system-ext.properties",
        order   => 00,
        content => "# Managed by puppet\n",
    }
}
