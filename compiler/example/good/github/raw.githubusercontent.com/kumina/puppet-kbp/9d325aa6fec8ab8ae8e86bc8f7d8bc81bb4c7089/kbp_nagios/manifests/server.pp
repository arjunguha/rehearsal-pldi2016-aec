# Author: Kumina bv <support@kumina.nl>

# Class: kbp_nagios::server::plugins
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_nagios::server::plugins inherits nagios::server::plugins {
}

# Class: kbp_nagios::server
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_nagios::server inherits nagios::server {
  include kbp_nagios::server::plugins
  class { "kbp_nsca::server":
    package => "nagios";
  }

  file {
    "/etc/nagios3/conf.d/contacts.cfg":
      content => template("kbp_nagios/nagios3/conf.d/contacts.cfg"),
      notify  => Exec["reload-nagios3"];
    "/etc/nagios3/conf.d/generic-host.cfg":
      content => template("kbp_nagios/nagios3/conf.d/generic-host.cfg"),
      notify  => Exec["reload-nagios3"];
    "/etc/nagios3/conf.d/generic-service.cfg":
      content => template("kbp_nagios/nagios3/conf.d/generic-service.cfg"),
      notify  => Exec["reload-nagios3"];
    "/etc/nagios3/conf.d/hostgroups.cfg":
      content => template("kbp_nagios/nagios3/conf.d/hostgroups.cfg"),
      notify  => Exec["reload-nagios3"];
    "/etc/nagios3/conf.d/misc_commands.cfg":
      content => template("kbp_nagios/nagios3/conf.d/misc_commands.cfg"),
      notify  => Exec["reload-nagios3"];
    "/etc/nagios3/conf.d/notify_commands.cfg":
      content => template("kbp_nagios/nagios3/conf.d/notify_commands.cfg"),
      notify  => Exec["reload-nagios3"];
    "/etc/nagios3/conf.d/passive_services.cfg":
      content => template("kbp_nagios/nagios3/conf.d/passive_services.cfg"),
      notify  => Exec["reload-nagios3"];
    "/etc/nagios3/conf.d/servicegroups.cfg":
      content => template("kbp_nagios/nagios3/conf.d/servicegroups.cfg"),
      notify  => Exec["reload-nagios3"];
    "/etc/nagios3/conf.d/services.cfg":
      content => template("kbp_nagios/nagios3/conf.d/services.cfg"),
      notify  => Exec["reload-nagios3"];
    "/etc/nagios3/conf.d/timeperiods.cfg":
      content => template("kbp_nagios/nagios3/conf.d/timeperiods.cfg"),
      notify  => Exec["reload-nagios3"];
    "/etc/cron.d/nagios-check-alive-cron":
      content => template("kbp_nagios/nagios-check-alive-cron");
    "/usr/bin/nagios-check-alive":
      content => template("kbp_nagios/nagios-check-alive"),
      mode    => 755;
  }
}
