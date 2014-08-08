# This resource installs default *-ext.properties resources in an instance, don't use it directly.
#
# === Authors
#
# Sander Bilo <sander@proteon.nl>
#
# === Copyright
#
# Copyright 2013 Proteon.
#
define liferay::property (
    $instance,
    $type = 'portal',
    $key,
    $value) {
    include tomcat
    
    if !($type in ['portal', 'portlet', 'system']) {
        fail("The property type must be one of 'portal', 'portlet' or 'system', but was '${type}'")
    }

    concat::fragment { $name:
        target  => "${tomcat::params::home}/${instance}/tomcat/lib/${type}-ext.properties",
        order   => 01,
        content => "${key}=${value}\n",
        notify  => Tomcat::Service[$instance],
    }
}
