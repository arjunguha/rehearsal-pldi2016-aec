# == Resource: liferay::cluster::cache
#
# === Parameters
#
# [*instance*]               The instance this Liferay lucene cluster configuration should be applied to (see liferay::instance).
# [*ehcache_cluster_link_replication_enabled*]   See Liferay portal.properties for documentation on this parameter.
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
define liferay::cluster::cache ($instance = $name, $ehcache_cluster_link_replication_enabled = true) {
    liferay::property { "${instance}:ehcache.cluster.link.replication.enabled":
        instance => $instance,
        key      => 'ehcache.cluster.link.replication.enabled',
        value    => true,
    }

    liferay::property { "${instance}:net.sf.ehcache.configurationResourceName":
        instance => $instance,
        key      => 'net.sf.ehcache.configurationResourceName',
        value    => '/ehcache/hibernate-clustered.xml',
    }

    liferay::property { "${instance}:ehcache.single.vm.config.location":
        instance => $instance,
        key      => 'ehcache.single.vm.config.location',
        value    => '/ehcache/liferay-single-vm.xml',
    }

    liferay::property { "${instance}:ehcache.multi.vm.config.location":
        instance => $instance,
        key      => 'ehcache.multi.vm.config.location',
        value    => '/ehcache/liferay-multi-vm-clustered.xml',
    }
}