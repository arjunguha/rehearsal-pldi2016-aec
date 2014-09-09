# == Resource: liferay::cluster
#
# === Parameters
#
# [*instance*]  The instance this liferay cluster should be applied to (see liferay::instance).
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
define liferay::cluster ($instance = $name) {
    if (!defined(Tomcat::Cluster[$instance])) {
        tomcat::cluster::simple { $instance: }
    }

    if (!defined(Liferay::Cluster::Lucene[$instance])) {
        liferay::cluster::lucene { $instance: }
    }

    if (!defined(Liferay::Cluster::Cache[$instance])) {
        liferay::cluster::cache { $instance: }
    }
    
    if (!defined(Liferay::Cluster::Jgroups[$instance])) {
        liferay::cluster::jgroups { $instance: }
    }
}