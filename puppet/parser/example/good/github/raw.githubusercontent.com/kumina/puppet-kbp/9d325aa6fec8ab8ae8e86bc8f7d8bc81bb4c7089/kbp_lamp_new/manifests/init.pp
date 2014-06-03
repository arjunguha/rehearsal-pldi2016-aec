# Author: Kumina bv <support@kumina.nl>

# Copyright (C) 2010 Kumina bv, Tim Stoop <tim@kumina.nl>
# This works is published under the Creative Commons Attribution-Share
# Alike 3.0 Unported license - http://creativecommons.org/licenses/by-sa/3.0/
# See LICENSE for the full legal text.

# Class: kbp_lamp::common
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_lamp_new::common {
  include kbp_apache
}

# Class: kbp_lamp::cgi
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_lamp_new::cgi {
  include kbp_apache

  package { "libapache2-mod-fcgid":
    ensure => latest,
    notify => Service["apache2"],
  }

  define enable_for ($documentroot = false) {
    file { "/etc/apache2/vhost-additions/$name/enable-cgi":
      content => $documentroot ? {
        false   => "<Directory /srv/www/${name}>\n AddHandler fcgid-script .php\n FCGIWrapper /usr/lib/cgi-bin/php5 .php\n Options ExecCGI Indexes FollowSymLinks MultiViews\n AllowOverride All\n Order allow,deny\n allow from all\n</Directory>\n",
        default => "<Directory ${documentroot}>\n AddHandler fcgid-script .php\n FCGIWrapper /usr/lib/cgi-bin/php5 .php\n Options ExecCGI Indexes FollowSymLinks MultiViews\n AllowOverride All\n Order allow,deny\n allow from all\n</Directory>\n",
      },
      owner   => "root",
      group   => "root",
      mode    => 644,
      notify  => Exec["reload-apache2"],
    }

    file { "/etc/apache2/vhost-additions/$name/enable-cgi-scriptalias":
      content => "ScriptAlias /cgi-bin/ /usr/lib/cgi-bin/\n<Directory \"/usr/lib/cgi-bin\">\n AllowOverride None\n Options ExecCGI -MultiViews +SymLinksIfOwnerMatch\n Order allow,deny\n Allow from all\n</Directory>\n",
      owner   => "root",
      group   => "root",
      mode    => 644,
      notify  => Exec["reload-apache2"],
    }
  }
}

# Class: kbp_lamp::php-cgi
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_lamp::php-cgi {
  include kbp_lamp::common
  include kbp_lamp::cgi

  package { ["php5-cgi","php-apc"]:
    ensure => latest,
  }

  # We specifically do not want mod-php5
  package { "libapache2-mod-php5":
    ensure => purged,
    notify => Service["apache2"],
  }
}
