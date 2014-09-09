# Author: Kumina bv <support@kumina.nl>

# Class: kbp_tomcat
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_tomcat ($tomcat_tag="tomcat_${environment}", $serveralias=false, $documentroot=false, $ssl=false, $ajp13_connector_port = "8009",
                  $java_opts="", $jvm_max_mem=false, $jvm_permgen_mem=false, $trending_password=false, $monitoring_password,
                  $ajp13_maxclients='200', $ajp13_uriencoding = false, $autodeploy=false, $max_open_files=false, $sms=true){

  if $trending_password {
    kbp_tomcat::user { 'munin':
      password   => $trending_password,
      role       => 'manager',
      tomcat_tag => $tomcat_tag;
    }
    class { 'kbp_munin::client::tomcat':
      trending_password => $trending_password;
    }
  }

  class {
    'kbp_collectd::plugin::tomcat':
      monitor_password    => $monitoring_password;
    'kbp_icinga::tomcat':
      monitoring_password => $monitoring_password,
      sms                 => $sms;
  }

  kbp_tomcat::user { 'monitoring':
    password   => $monitoring_password,
    role       => 'manager',
    tomcat_tag => $tomcat_tag;
  }

  class { "gen_tomcat":
    ajp13_connector_port => $ajp13_connector_port,
    java_opts            => $java_opts,
    jvm_max_mem          => $jvm_max_mem,
    jvm_permgen_mem      => $jvm_permgen_mem,
    ajp13_maxclients     => $ajp13_maxclients,
    ajp13_uriencoding    => $ajp13_uriencoding,
    max_open_files       => $max_open_files,
    autodeploy           => $autodeploy,
    tomcat_tag           => $tomcat_tag;
  }

  # Add /usr/share/java/*.jar to the tomcat classpath
  file { "/srv/tomcat/conf/catalina.properties":
    content => template("kbp_tomcat/catalina.properties"),
    require => [Package["tomcat6"], File["/srv/tomcat/conf"]];
  }

  # Ensure that everyone in the group tomcat6 can restart Tomcat
  kbp_sudo::rule { "Allow tomcat manipulation when in the tomcat6 group":
    command           => "/etc/init.d/tomcat6 [a-z]*",
    as_user           => "root",
    entity            => "%tomcat6",
    password_required => false;
  }
}

# Class: kbp_tomcat::mysql
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_tomcat::mysql {
#  include kbp_tomcat
#  include kbp_mysql::client::java
}

# Define: kbp_tomcat::webapp
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
#  gen_tomcat
#  gen_puppet
#
define kbp_tomcat::webapp($war="", $urlpath="/", $context_xml_content=false, $root_app=false, $tomcat_tag="tomcat_${environment}",
                          $additional_context_settings = false, $environment_settings = false, $valve_settings = false,
                          $datasource_settings = false, $leave_settings_alone=false, $monitoring_password=false) {
  gen_tomcat::context { $name:
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
      kbp_tomcat::additional_context_setting { $contextkeys:
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
      kbp_tomcat::environment_setting { $environmentkeys:
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
      kbp_tomcat::valve_setting { $valvekeys:
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
      kbp_tomcat::datasource_setting { $datasourcekeys:
        context => $name,
        hash    => $datasource_settings,
      }
    }
  }
}

# Define: kbp_tomcat::additional_context_setting
#
# Actions:
#  A dirty workaround for #9768 (puppet bug).
#
define kbp_tomcat::additional_context_setting ($context, $hash) {
  gen_tomcat::additional_context_setting { "${name}":
    context      => $context,
    setting_name => $name,
    value        => $hash[$name],
  }
}

# Define: kbp_tomcat::environment_setting
#
# Actions:
#  A dirty workaround for #9768 (puppet bug).
#
define kbp_tomcat::environment_setting ($context, $hash) {
  gen_tomcat::environment { "${name}":
    context  => $context,
    var_name => $name,
    value    => $hash[$name]["value"],
    var_type => $hash[$name]["var_type"],
  }
}

# Define: kbp_tomcat::valve_setting
#
# Actions:
#  A dirty workaround for #9768 (puppet bug).
#
define kbp_tomcat::valve_setting ($context, $hash) {
  gen_tomcat::valve { "${name}":
    context   => $context,
    classname => $name,
    allow     => $hash[$name]["allow"],
  }
}

# Define: kbp_tomcat::datasource_setting
#
# Actions:
#  A dirty workaround for #9768 (puppet bug).
#
define kbp_tomcat::datasource_setting ($context, $hash) {
  gen_tomcat::datasource { "${name}":
    context    => $context,
    resource   => $name,
    username   => $hash[$name]["username"],
    password   => $hash[$name]["password"],
    url        => $hash[$name]["url"],
    max_active => $hash[$name]["max_active"],
    max_idle   => $hash[$name]["max_idle"],
  }
}

# Class: kbp_tomcat::apache_common
#
# Actions: activate mod-proxy-ajp
#
# Called from kbp_tomcat::apache_proxy_ajp_site, don't use by itself
#
class kbp_tomcat::apache_common {
  # Enable mod-proxy-ajp
  kbp_apache::module { "proxy_ajp":; }
}

# Define: kbp_tomcat::apache_proxy_ajp_site
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
define kbp_tomcat::apache_proxy_ajp_site($ensure="present", $tomcat_host='localhost', $port=8009, $ssl=false, $address='*', $redirect_non_ssl=true, $non_ssl=true, $serveralias=false, $documentroot="/srv/www/${name}",
    $tomcat_tag="tomcat_${environment}", $sourcepath="/", $urlpath="/", $php=false, $make_default=false, $monitor_path=$urlpath, $monitor_response=false, $monitor_max_check_attempts="5", $auth=false, $intermediate=false, $cert=false,
    $wildcard=false, $monitor_statuscode=false, $ha=false, $monitor=true) {

  include kbp_tomcat::apache_common

  if $ssl or $intermediate {
    $real_ssl = true
  } else {
    $real_ssl = false
  }


  kbp_apache::site { $name:
    ensure             => $ensure,
    serveralias        => $serveralias,
    documentroot       => $documentroot,
    php                => $php,
    make_default       => $make_default,
    ha                 => $ha,
    monitor            => $monitor,
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

  if $non_ssl {
    kbp_apache::vhost_addition { "${name}/tomcat_proxy":
      ports   => $non_ssl ? {
        true  => $real_ssl ? {
          true  => [80, 443],
          false => 80,
        },
        false => 443,
      },
      content => template("kbp_tomcat/apache/tomcat_proxy");
    }
  }
}

# Define: kbp_tomcat::user
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
define kbp_tomcat::user ($username=false, $password, $role, $tomcat_tag="tomcat_${environment}") {
  if !$username {
    $the_username = $name
  } else {
    $the_username = $username
  }

  gen_tomcat::user { "${the_username}":
    username   => $the_username,
    password   => $password,
    role       => $role,
    tomcat_tag => $tomcat_tag;
  }
}

# Define: kbp_tomcat::role
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
define kbp_tomcat::role ($role=false, $tomcat_tag="tomcat_${environment}") {
  if !$role {
    $the_role = $name
  } else {
    $the_role = $role
  }

  gen_tomcat::role { "${the_role}":
    role       => $the_role,
    tomcat_tag =>  $tomcat_tag;
  }
}
