# == Synopsis
# This is for setting up LogStash.
#
# == Parameters
#
# [*amqp_server*]
#  Use this to specify the address or fqdn of the message broker. Defaults to
#  broker.${domain}.
#
# [*elasticsearch_server*]
#  Use this to specify the address or fqdn of the elasticsearch server.
#  Defaults to localhost.
#
# [*ensure*]
#  Use this to specify whether the class' resources should be applied or
#  removed.
#
# [*roles*]
#  Use this to specify which logstash tasks will be performed. Valid values
#  are 'shipper', 'indexer', and 'web'. Defaults to shipper.
#
# == Examples
#
#   class {
#      "logstash":
#         ensure => "present";
#   }
#
# == Notes
#
#  This code assumes you have a logstash deb in an available repo.
#
# == Authors
#
# Joe McDonagh <jmcdonagh@thesilentpenguin.com>
#
# == Copyright
#
# Copyright 2012 The Silent Penguin LLC
#
# == License
# Licensed under The Silent Penguin Properietary License
#
class logstash (
   $amqp_server            = "broker.${domain}",
   $elasticsearch_server   = "localhost",
   $ensure                 = "present",
   $roles                  = [ "shipper" ]
) {
   # Parameter Validation
   $supported_minimum_os_versions   = { "Ubuntu" => 10.04 }
   $supported_operatingsystems      = [ "Ubuntu" ]
   $valid_ensure_values             = [ "present", "absent" ]

   if ! ($::operatingsystem in $supported_operatingsystems) {
      fail "Your OS ($::operatingsystem) is not supported by this code!"
   }

   if ($::operatingsystemrelease < $supported_minimum_os_versions[$::operatingsystem] ) {
      fail "You need at least version $supported_minimum_os_versions[$::operatingsystem] to use this code."
   }

   if ! ($ensure in $valid_ensure_values) {
      fail "Invalid ensure value for logstash, valid values are $valid_ensure_values"
   }

   # Variables for resources based on $ensure
   if ($ensure == "present") {
      $file_notify_indexer = Service["logstash-indexer"]
      $file_notify_shipper = Service["logstash-shipper"]
      $file_notify_web     = Service["logstash-web"]
      $file_require        = Package["logstash"]
      $svc_before          = undef
      $svc_enable          = "true"
      $svc_ensure          = "running"
      $svc_require         = [ File["/var/log"], Package["logstash"] ]
   } else {
      $file_notify_indexer = undef
      $file_notify_shipper = undef
      $file_notify_web     = undef
      $file_require        = undef
      $svc_before          = Package["logstash"]
      $svc_enable          = "false"
      $svc_ensure          = "stopped"
      $svc_require         = undef
   }

   if ("indexer" in $roles) {
      file {
         "/etc/default/logstash-indexer":
            content  => template("logstash/indexer.default.erb"),
            ensure   => $ensure,
            mode     => "644",
            notify   => $file_notify_indexer,
            require  => $file_require;
         "/etc/logstash/indexer.cfg":
            content  => template("logstash/indexer.cfg.erb"),
            ensure   => $ensure,
            mode     => "644",
            notify   => $file_notify_indexer,
            require  => $file_require;
      }
   
      service {
         "logstash-indexer":
            before      => $svc_before,
            enable      => $svc_enable,
            ensure      => $svc_ensure,
            hasstatus   => "true",
            require     => $svc_require;
      }
   }

   if ("shipper" in $roles) {
      file {
         "/etc/default/logstash-shipper":
            content  => template("logstash/shipper.default.erb"),
            ensure   => $ensure,
            mode     => "644",
            notify   => $file_notify_shipper,
            require  => $file_require;
         "/etc/logstash/shipper.cfg":
            content  => template("logstash/shipper.cfg.erb"),
            ensure   => $ensure,
            mode     => "644",
            notify   => $file_notify_shipper,
            require  => $file_require;
      }
   
      service {
         "logstash-shipper":
            before      => $svc_before,
            enable      => $svc_enable,
            ensure      => $svc_ensure,
            hasstatus   => "true",
            require     => $svc_require;
      }
   }

   if ("web" in $roles) {
      file {
         "/etc/default/logstash-web":
            content  => template("logstash/web.default.erb"),
            ensure   => $ensure,
            mode     => "644",
            notify   => $file_notify_web,
            require  => $file_require;
         "/etc/logstash/web.cfg":
            content  => template("logstash/web.cfg.erb"),
            ensure   => $ensure,
            mode     => "644",
            notify   => $file_notify_web,
            require  => $file_require;
      }
   
      service {
         "logstash-web":
            before      => $svc_before,
            enable      => $svc_enable,
            ensure      => $svc_ensure,
            hasstatus   => "true",
            require     => $svc_require;
      }
   }

   file {
      "/var/log":
         ensure   => "directory",
         group    => "logstash",
         mode     => "644",
         owner    => undef,
         recurse  => "true",
         require  => Package["logstash"]; 
   }

   package {
      "grok":
         ensure   => $ensure;
      "logstash":
         ensure   => $ensure;
   }
}

#vim: set expandtab ts=3 sw=3:
