
# == Resource: liferay::cluster::jgroups
#
# === Parameters
#
# [*instance*]               The instance this Liferay lucene cluster configuration should be applied to (see liferay::instance).
# [*java_net_preferIPv4Stack*]   Needed for the 6.1.x version of Jgroups.
#
# === Variables
#
# === Examples
#
# === Authors
#
# Sander Bilo <sander@proteon.nl>
#
# === Copyright
#
# Copyright 2013 Proteon.
#
define liferay::cluster::jgroups ($instance = $name, $java_net_preferIPv4Stack = true) {
    liferay::property { "${instance}:java.net.preferIPv4Stack":
        instance => $instance,
        key      => 'java.net.preferIPv4Stack',
        value    => $java_net_preferIPv4Stack,
        type     => 'system',
    }
}
