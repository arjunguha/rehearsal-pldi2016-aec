# From https://github.com/gavinzhou/puppet-module/tree/ad3f8244809adc6cb452d2e1b2feee0d6de363bd/apache/manifests

include apache

class apache {
  include apache::install, apache::config
}

class apache::config {
    $require = Class["apache::install"]

# TODO(jcollard): We don't support this  
#    File {
#        ensure  => "present",
#        owner   => "root",
#        group   => "root",
#        mode    => "0644",
#    }

    file { 
        "/crooz":
        ensure => directory;

		"/etc/httpd/conf/httpd.conf":
        require => File["/crooz"],
		source  => "puppet:///modules/apache/conf/httpd.conf";

        "/crooz/application-level.inc":
        source  => "puppet:///modules/apache/crooz/application-level.inc";
		
		"/etc/httpd/conf/magic":
		source  => "puppet:///modules/apache/conf/magic";
		
		"/etc/httpd/conf.d":
		recurse => "true",
		source  => "puppet:///modules/apache/conf.d";

		"/etc/httpd/conf.d/proxy_ajp.conf":
		ensure  => absent;

		"/etc/httpd/conf.d/ssl.conf":
		ensure  => absent;

		"/etc/httpd/conf.d/welcome.conf":
		ensure  => absent;

		"/var/www/seo":
		recurse => "true",
		source  => "puppet:///modules/apache/www/seo";

		"/var/www/healthcheck":
		recurse => "true",
		source  => "puppet:///modules/apache/www/healthcheck";

		"/var/www/local":
		recurse => "true",
		source  => "puppet:///modules/apache/www/local";

        "/var/www/local/flashpolicy":
        owner   => "apache",
        group   => "apache",
        mode    => "0700";

		"/var/log/httpd":
        owner   => "apache",
        group   => "apache",
        mode    => "0755";
    }
# HACK(jcollard): We do not support cron    
#    cron { 
#        "apache-log-arh":
#        command => "gzip /var/log/httpd/*log.$(date +\%Y\%m\%d -d '3 days ago')",
#        user    => "root",
#        hour    => "4",
#        minute  => "0";
#
#        "apache-log-del": 
#        command => "/bin/rm /var/log/httpd/*log.$(date +\%Y\%m\%d -d '30 days ago').gz",
#        user    => "root",
#        hour    => "4",
#        minute  => "20";
#    }

    augeas { "tcp_max_tw":
        context => "/files/etc/sysctl.conf",
        changes => [
            "set net.ipv4.tcp_max_tw_buckets 20000",
        ];
    }
}

define apache::vhost( $port=80, 
                      $docroot, 
                      $template='apache/virtualhost.conf.erb', 
                      $ver='',
                      $serveraliases = '' ) {
    include apache

    if $ver != '' {
        $_ver = "_v${ver}"
    }    

    file {"/etc/httpd/conf.d/virtualhost_${name}${_ver}.conf":
            content => template($template),
            owner   => 'root',
            group   => 'root',
            mode    => '0644',
            require => Class["apache::install"],
    }
}

class apache::install {
    package { "apache":
        name    => [ "httpd", "httpd-devel.x86_64", "mod_ssl", "distcache", "mod_extract_forwarded",],
      ensure  => "installed",
      require => [Class["yumrepo"], Class["php"],],
    }
}

# HACK(jcollard): Force instantiation.
include php, yumrepo

class php::config {
    $require = Class["php::install"]

# HACK(jcollard): We do not support this
#    File {
#        ensure  => present,
#        owner   => 'root',
#        group   => 'root',
#        mode    => 0644,
#    }

    file { 
		"/etc/php.ini":
		source  => "puppet:///modules/php/php.ini";
    }
}

class php {
	include php::install, php::config
}

class php::redis {
    package { "php-redis":
        ensure  => "installed",
        require => Class["yumrepo"],
    }
}

class php::install {
	package { "php":
		name    => ["php", "php-devel", "php-gd", "php-mbstring", "php-mcrypt", "php-mysql", "php-ncurses", "php-pdo", "php-pear", "php-pecl-memcache", "php-soap", "php-xml", "php-xmlrpc",],
		ensure  => installed,
        require => Class["yumrepo"],
	}
}

class yumrepo {

# HACK(jcollard): We do not support this  
#	File {
#		owner   => "root",
#		group   => "root",
#		mode    => "0644",
#	}

	file {
		"/etc/yum.repos.d/centos5.x-local.repo":
		source  => "puppet:///modules/yumrepo/centos5.x-local.repo";

		"/etc/yum.repos.d/crooz.repo":
		source  => "puppet:///modules/yumrepo/crooz.repo";

		"/etc/yum.repos.d/puppetlabs.repo":
		source  => "puppet:///modules/yumrepo/puppetlabs.repo";

		"/etc/yum.repos.d/epel.repo":
		source  => "puppet:///modules/yumrepo/epel.repo";

        "/etc/yum.repos.d/CentOS-Base.repo":
        ensure  => absent;

        "/etc/yum.repos.d/CentOS-Media.repo":
        ensure  => absent;
	}
}
