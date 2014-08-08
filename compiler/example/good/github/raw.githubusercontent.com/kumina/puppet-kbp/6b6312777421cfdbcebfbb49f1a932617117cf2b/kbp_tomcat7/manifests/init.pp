# Author: Kumina bv <support@kumina.nl>

# Class: kbp_tomcat7
#
# Actions:
#  Setup Tomcat 7.
#
# Parameters:
#  ajp13_connector_port
#    The port to setup for ajp13 connections. Defaults to 8009.
#  ajp13_maxclients
#    The MaxClients setting for Tomcat's AJP port. Does not affect HTTP. Defaults to 200.
#  java_opts
#    The JVM options to add to the jvm invocation.
#  jvm_max_mem
#    Maximum memory to allow the JVM to use.
#  jvm_permgen_mem
#    Set the PermGen size for the JVM.
#  tomcat_tag
#    The tag used for exporting the Tomcat users in tomcat-users.xml
#  max_open_files
#    Max. allowed open files (ulimit -n). Defaults to 4096.
#  autodeploy
#    Whether to enable autodeploy. Defaults to true.
#  trending_password
#    Set this to a secure password for the trending.
#  monitoring_password
#    Set this to a secure password for the monitoring.
#
# Depends:
#  gen_tomcat7
#
class kbp_tomcat7 ($tomcat_tag="tomcat_${environment}", $ajp13_connector_port = "8009", $java_opts="", $jvm_max_mem=false, $jvm_permgen_mem=false,
                   $trending_password, $monitoring_password, $ajp13_maxclients='200', $autodeploy=true, $max_open_files=4096){
  if $trending_password {
    kbp_tomcat7::user { 'munin':
      password   => $trending_password,
      role       => 'manager-jmx',
      tomcat_tag => $tomcat_tag;
    }
    class { 'kbp_munin::client::tomcat':
      trending_password => $trending_password;
    }
  }

  class {
    'kbp_icinga::tomcat':
      monitoring_password => $monitoring_password;
    'kbp_collectd::plugin::tomcat':
      monitor_password    => $monitoring_password;
  }

  kbp_tomcat7::user { 'monitoring':
    password   => $monitoring_password,
    role       => 'manager-status',
    tomcat_tag => $tomcat_tag;
  }

  class { "gen_tomcat7":
    ajp13_connector_port => $ajp13_connector_port,
    java_opts            => $java_opts,
    jvm_max_mem          => $jvm_max_mem,
    jvm_permgen_mem      => $jvm_permgen_mem,
    ajp13_maxclients     => $ajp13_maxclients,
    max_open_files       => $max_open_files,
    autodeploy           => $autodeploy,
    tomcat_tag           => $tomcat_tag;
  }

  # Add /usr/share/java/*.jar to the tomcat classpath
  #file { "/srv/tomcat/conf/catalina.properties":
  #  content => template("kbp_tomcat/catalina.properties"),
  #  require => [Package["tomcat7"], File["/srv/tomcat/conf"]];
  #}

  # Ensure that everyone in the group tomcat7 can restart Tomcat
  kbp_sudo::rule { "Allow tomcat manipulation when in the tomcat7 group":
    command           => "/etc/init.d/tomcat7 [a-z]*",
    as_user           => "root",
    entity            => "%tomcat7",
    password_required => false;
  }
}

# Class: kbp_tomcat7::mysql
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_tomcat7::mysql {
#  include kbp_tomcat
#  include kbp_mysql::client::java
}

# Define: kbp_tomcat7::webapp
#
# Actions:
#  Setup a Tomcat webapp.
#
# Parameters:
#  war
#    The warfile to use for this app.
#  urlpath
#    The path on which the app should be mounted in Tomcat
#  context_xml_content
#    DEPRECATED Extra XML stuff inside the <Context/>. Don't use.
#  root_app
#    Set to true if the ROOT app should point to this app.
#  tomcat_tag
#    The default tag to use.
#  additional_context_settings
#    Additional options to set inside the <Context/> tag. Like debug and stuff. Should be a hash like:
#    { "debug" => { value => "5" }, "reloadable" => { value => true } }
#  environment_settings
#    Environment variables to set within this Tomcat Context. Should be a hash like:
#    { "emailHost" => { value => "smtp", var_type => "java.lang.String" } }
#  valve_settings
#    Valves to open for specific IP addresses within this Tomcat Context.
#  datasource_settings
#    JNDI Datasources for this Tomcat Context. Should be a hash like:
#    { "jdbc/WBISDataSource" => { username => "wbis", password => "verysecret", url => "jdbc:mysql://mysql-rw/wbis",
#                                 max_active => "8", max_idle => "4", driver => "com.mysql.jdbc.Driver" } }
#
# Depends:
#  gen_tomcat7
#  gen_puppet
#
define kbp_tomcat7::webapp($war="", $urlpath="/", $context_xml_content=false, $root_app=false, $tomcat_tag="tomcat_${environment}",
                           $additional_context_settings = false, $environment_settings = false, $valve_settings = false,
                           $datasource_settings = false, $leave_settings_alone=false, $monitoring_password=false) {
  gen_tomcat7::context { $name:
    tomcat_tag          => $tomcat_tag,
    war                 => $war,
    urlpath             => $urlpath,
    context_xml_content => $context_xml_content,
    root_app            => $root_app;
  }

  if $monitoring_password {
    kbp_icinga::tomcat::application { $name:
      monitoring_password => $monitoring_password;
    }
  }

  if ! $leave_settings_alone {
    if $additional_context_settings {
      # This is a very elaborate workaround for not being able to add an option
      # to create_resources. Solved when puppet bug #9768 is fixed.
      # This would then be enough:
      #  - create_resources("gen_tomcat::additional_context_setting",$additional_context_settings, {context => $name})
      $contextkeys = hash_keys($additional_context_settings)
      kbp_tomcat7::additional_context_setting { $contextkeys:
        context => $name,
        hash    => $additional_context_settings,
      }
    }

    if $environment_settings {
      # This is a very elaborate workaround for not being able to add an option
      # to create_resources. Solved when puppet bug #9768 is fixed.
      # This would then be enough:
      #  - create_resources("gen_tomcat::environment",$environment_settings, {context => $name})
      $environmentkeys = hash_keys($environment_settings)
      kbp_tomcat7::environment_setting { $environmentkeys:
        context => $name,
        hash    => $environment_settings,
      }
    }

    if $valve_settings {
      # This is a very elaborate workaround for not being able to add an option
      # to create_resources. Solved when puppet bug #9768 is fixed.
      # This would then be enough:
      #  - create_resources("gen_tomcat::valve",$valve_settings, {context => $name})
      $valvekeys = hash_keys($valve_settings)
      kbp_tomcat7::valve_setting { $valvekeys:
        context => $name,
        hash    => $valve_settings,
      }
    }

    if $datasource_settings {
      # This is a very elaborate workaround for not being able to add an option
      # to create_resources. Solved when puppet bug #9768 is fixed.
      # This would then be enough:
      #  - create_resources("gen_tomcat::datasource",$datasource_settings, {context => $name})
      $datasourcekeys = hash_keys($datasource_settings)
      kbp_tomcat7::datasource_setting { $datasourcekeys:
        context => $name,
        hash    => $datasource_settings,
      }
    }
  }
}

# Define: kbp_tomcat7::additional_context_setting
#
# Actions:
#  A dirty workaround for #9768 (puppet bug).
#
define kbp_tomcat7::additional_context_setting ($context, $hash) {
  gen_tomcat7::additional_context_setting { "${name}":
    context      => $context,
    setting_name => $name,
    value        => $hash[$name],
  }
}

# Define: kbp_tomcat7::environment_setting
#
# Actions:
#  A dirty workaround for #9768 (puppet bug).
#
define kbp_tomcat7::environment_setting ($context, $hash) {
  gen_tomcat7::environment { "${name}":
    context  => $context,
    var_name => $name,
    value    => $hash[$name]["value"],
    var_type => $hash[$name]["var_type"],
  }
}

# Define: kbp_tomcat7::valve_setting
#
# Actions:
#  A dirty workaround for #9768 (puppet bug).
#
define kbp_tomcat7::valve_setting ($context, $hash) {
  gen_tomcat7::valve { "${name}":
    context   => $context,
    classname => $name,
    allow     => $hash[$name]["allow"],
  }
}

# Define: kbp_tomcat7::datasource_setting
#
# Actions:
#  A dirty workaround for #9768 (puppet bug).
#
define kbp_tomcat7::datasource_setting ($context, $hash) {
  gen_tomcat7::datasource { "${name}":
    context    => $context,
    resource   => $name,
    username   => $hash[$name]["username"],
    password   => $hash[$name]["password"],
    url        => $hash[$name]["url"],
    max_active => $hash[$name]["max_active"],
    max_idle   => $hash[$name]["max_idle"],
  }
}

# Class: kbp_tomcat7::apache_common
#
# Actions: activate mod-proxy-ajp
#
# Called from kbp_tomcat7::apache_proxy_ajp_site, don't use by itself
#
class kbp_tomcat7::apache_common {
  # Enable mod-proxy-ajp
  kbp_apache::module { "proxy_ajp":; }
}

# Define: kbp_tomcat7::apache_proxy_ajp_site
#
# Actions:
#  Setup apache with mod_proxy_ajp (and mod_proxy_balancer if needed) for a tomcat app
#
# Parameters:
#  name: The name of the vhost. If this contains a '_', it is stripped, use this
#        to export the vhost from multiple tomcat servers. This is only needed if $proxy_balancer_name is set.
#  tomcat_host: The host the webapp runs on
#  port: The port the app runs on
#  ssl: Should apache use SSL
#  address: the IP address for this vhost
#  sourcepath: The path in the URL (from the client) where the app should live
#  urlpath: The path on the tomcat server where the app lives
#  proxy_balancer_name: Set this to use proxy balancer (see the note about $name)
#
# Depends:
#  Undocumented
#  gen_puppet
#
define kbp_tomcat7::apache_proxy_ajp_site($ensure="present", $tomcat_host='localhost', $port=8009, $ssl=false, $address='*', $redirect_non_ssl=true, $non_ssl=true, $serveralias=false, $documentroot=false,
    $tomcat_tag="tomcat_${environment}_${custenv}", $sourcepath="/", $urlpath="/", $php=false, $make_default=false, $monitor_path=$urlpath, $monitor_response=false, $monitor_max_check_attempts="5", $auth=false, $intermediate=false,
    $cert=false, $wildcard=false, $monitor_statuscode=false, $ha=false, $proxy_balancer_name=false) {
  include kbp_tomcat7::apache_common

  if $ssl or $intermediate {
    $real_ssl = true
  } else {
    $real_ssl = false
  }

  if $name =~ /_/ {
    $real_name = regsubst($name,'([^_]*)_.*','\1')
  } else {
    $real_name = $name
  }

  if ! defined(Kbp_apache::Site[$real_name]) {
    kbp_apache::site { $real_name:
      ensure             => $ensure,
      serveralias        => $serveralias,
      documentroot       => $documentroot ? {
        false   => "/srv/www/${real_name}",
        default => $documentroot,
      },
      php                => $php,
      make_default       => $make_default,
      ha                 => $ha,
      monitor_path       => $monitor_path,
      monitor_response   => $monitor_response,
      monitor_statuscode => $monitor_statuscode,
      max_check_attempts => $monitor_max_check_attempts,
      auth               => $auth,
      address            => $address,
      ssl                => $ssl,
      redirect_non_ssl   => $redirect_non_ssl,
      non_ssl            => $non_ssl,
      cert               => $cert,
      wildcard           => $wildcard,
      intermediate       => $intermediate,
      require            => Kbp_apache::Module["proxy_ajp"];
    }

    kbp_apache::vhost_addition { "${real_name}/tomcat_proxy":
      ports   => $non_ssl ? {
        true  => $real_ssl ? {
          true  => [80, 443],
          false => 80,
        },
        false => 443,
      },
      content => $proxy_balancer_name ? {
        false   => template("kbp_tomcat7/apache/tomcat_proxy"),
        default => template("kbp_tomcat7/apache/tomcat_proxy_balancer"),
      };
    }
  }

  if $proxy_balancer_name {
    if ! defined(Kbp_apache::Vhost_addition["${real_name}/tomcat_balancer_${proxy_balancer_name}"]) {
      kbp_apache::vhost_addition { "${real_name}/tomcat_balancer_${proxy_balancer_name}":
        ports   => $non_ssl ? {
          true  => $real_ssl ? {
            true  => [80, 443],
            false => 80,
          },
          false => 443,
        },
        content => template("kbp_tomcat7/apache/tomcat_balancer");
      }
    }
    kbp_apache::vhost_addition { "${real_name}/tomcat_balancer_${proxy_balancer_name}_${tomcat_host}":
      ports   => $non_ssl ? {
        true  => $real_ssl ? {
          true  => [80, 443],
          false => 80,
        },
        false => 443,
      },
      content  => template("kbp_tomcat7/apache/tomcat_balancer_member");
    }
  }
}

# Define: kbp_tomcat7::user
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
define kbp_tomcat7::user ($username=false, $password, $role, $tomcat_tag="tomcat_${environment}_${custenv}") {
  if !$username {
    $the_username = $name
  } else {
    $the_username = $username
  }

  gen_tomcat7::user { "${the_username}":
    username   => $the_username,
    password   => $password,
    role       => $role,
    tomcat_tag => $tomcat_tag;
  }
}

# Define: kbp_tomcat7::role
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
define kbp_tomcat7::role ($role=false, $tomcat_tag="tomcat_${environment}_${custenv}") {
  if !$role {
    $the_role = $name
  } else {
    $the_role = $role
  }

  gen_tomcat7::role { "${the_role}":
    role       => $the_role,
    tomcat_tag =>  $tomcat_tag;
  }
}
