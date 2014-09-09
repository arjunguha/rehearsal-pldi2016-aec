# == Class: serverdensity_agent::config_file
#
# Defines the agent config file
#
# === Authors
#
# Server Density <hello@serverdensity.com>
#
# === Copyright
#
# Copyright 2014 Server Density
#

class serverdensity_agent::config_file (
        $location = '',
        $sd_url = 'https://example.serverdensity.io',
        $agent_key = '',
        $plugin_directory = '',
        $apache_status_url = 'http://www.example.com/server-status/?auto',
        $apache_status_user = '',
        $apache_status_pass = '',
        $fpm_status_url = '',
        $mongodb_server = '',
        $mongodb_dbstats = 'no',
        $mongodb_replset = 'no',
        $mysql_server = '',
        $mysql_user = '',
        $mysql_pass = '',
        $nginx_status_url = '',
        $rabbitmq_status_url = 'http://www.example.com/nginx_status',
        $rabbitmq_user = 'guest',
        $rabbitmq_pass = 'guest',
        $tmp_directory = '/var/log/custom_location',
        $pidfile_directory = '/var/log/custom_location',
        $logging_level = 'fatal',
    ) {

    file { 'sd-agent-config-dir':
      ensure  => 'directory',
      path    => $location,
      mode    => '0755',
      notify  => Class['serverdensity_agent::service'],
    }

    file { 'sd-agent-config-file':
        path    => "${location}/000-main.cfg",
        content => template('serverdensity_agent/config.cfg.erb'),
        mode    => '0644',
        notify  => Class['serverdensity_agent::service'],
    }
}
