# == Resource: liferay::cluster::lucene
#
# === Parameters
#
# [*instance*]               The instance this Liferay lucene cluster configuration should be applied to (see liferay::instance).
# [*cluster_link_enabled*]   See Liferay portal.properties for documentation on this parameter.
# [*lucene_replicate_write*] See Liferay portal.properties for documentation on this parameter.
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
define liferay::cluster::lucene ($instance = $name, $cluster_link_enabled = true, $lucene_replicate_write = true) {
    liferay::property { "${instance}:cluster.link.enabled":
        instance => $instance,
        key      => 'cluster.link.enabled',
        value    => $cluster_link_enabled,
    }

    liferay::property { "${instance}:lucene.replicate.write":
        instance => $instance,
        key      => 'lucene.replicate.write',
        value    => $lucene_replicate_write,
    }
}