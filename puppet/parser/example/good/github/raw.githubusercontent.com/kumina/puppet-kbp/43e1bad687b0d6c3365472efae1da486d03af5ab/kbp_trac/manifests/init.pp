#
# Class: kbp_trac
#
# Actions:
#  Setup trac for usage. Also installs some useful plugins.
#
# Depends:
#  gen_trac
#  kbp_apache
#
class kbp_trac {
  include gen_trac::xmlrpc
  include gen_trac::tags
}

# Class: kbp_trac::svn_dav
#
# Actions: Increase Apache's timeout value, since that could break connections on large repositories.
#
class kbp_trac::svn_dav {
  file { '/etc/apache2/conf.d/timeout':
    content => 'Timeout 3600',
    require => Package['apache2'],
    notify  => Exec['reload-apache2'];
  }
}

# Define: kbp_trac::environment
#
# Actions: Setup a trac environment for the named site. Also sets up the Apache vhost configuration and subversion repository.
#
# Parameters:
#  group: The system group which should have access.
#  vhost: The vhost in which this repository should be found.
#  port: The port on which the vhost listens that should be configured for use with trac.
#  svnrepo: The path to the subversion repository. False if no svn is used.
#  gitrepo: The path to the git repository. False if no git is used.
#  authfile: Setto true to use a file with user/password combinations. False for no authentication.
#  authip: A list with IP addresses to always allow access. False for no IP list.
#  authz_file: Location of the authz file. Defaults to /srv/www/${vhost}/${name}/authz.
#  logo_file: Template with the logo. Defaults to false.
#  logo_filename: The name of the logo file.
#  logo_link: Link for the logo. Defaults to an empty string (no link).
#  logo_alt: Alt text for logo. Defaults to an empty string.
#  trac_name: The title to be used for the site, defaults to the $name.
#  description: The description to use for the site, defaults to the $name.
#
# Depends:
#  gen_trac
#  kbp_apache
#  kbp_subversion
#
define kbp_trac::environment ($group, $vhost, $port, $svnrepo=false, $gitrepo=false, $authfile=false, $authip=false, $dbtype='sqlite', $dbuser=$name, $dbpassword=false, $dbhost='localhost', $dbname=$name,
                              $authz_file="/srv/www/${vhost}/${name}/authz", $logo_file=false, $logo_filename='', $logo_link='', $logo_alt='(Consult with Kumina to replace this image.)', $trac_name=$name,
                              $description=$name, $manage_ini=true) {
  include kbp_trac

  # Setup the Trac environment
  gen_trac::environment { $name:
    group         => $group,
    svnrepo       => $svnrepo,
    gitrepo       => $gitrepo,
    authz_file    => $authz_file,
    dbtype        => $dbtype,
    dbuser        => $dbuser,
    dbpassword    => $dbpassword,
    dbhost        => $dbhost,
    dbname        => $dbname,
    logo_file     => $logo_file,
    logo_filename => $logo_filename,
    logo_link     => $logo_link,
    logo_alt      => $logo_alt,
    trac_name     => $trac_name,
    manage_ini    => $manage_ini,
    description   => $description;
  }

  if defined(Kbp_apache::Site[$vhost]) {
    # Make sure we have a place to store the wsgi scripts
    file { "/srv/www/${vhost}/${name}":
      ensure => directory,
      group  => $group,
      owner  => 'www-data';
    }

    # Create the wsgi scripts, if needed
    exec { "/usr/bin/trac-admin /srv/trac/${name} deploy /srv/www/${vhost}/${name}":
      creates => "/srv/www/${vhost}/${name}/cgi-bin/trac.wsgi",
      require => [Exec["create-trac-${name}"],File["/srv/www/${vhost}/${name}"]];
    }

    kbp_apache::vhost_addition { "${vhost}/trac-${name}":
      ports   => $port,
      content => template('kbp_trac/apache.conf');
    }

    if $authfile or $authip {
      if $authip and (! is_array($authip)) {
        fail('Parameter authip should always be an array.')
      }

      kbp_apache::vhost_addition { "${vhost}/trac-${name}-auth":
        require => File["/srv/www/${vhost}/${name}/htusers"],
        ports   => $port,
        content => template('kbp_trac/apache-auth.conf');
      }

      file { "/srv/www/${vhost}/${name}/htusers":
        ensure  => file,
        group   => $group,
        mode    => 664;
      }

      kbp_trac::accountmanager_setup { $name:
        access_file => "/srv/www/${vhost}/${name}/htusers",
        path        => "/srv/trac/${name}";
      }
    } else {
      # Open up for the world
      kbp_apache::vhost_addition { "${vhost}/trac-${name}-auth":
        ports   => $port,
        content => template('kbp_trac/apache-allow-all.conf');
      }
    }

    if $svnrepo {
      include kbp_trac::svn_dav

      # SVN Authz file can be created even when we do not use svn.
      file { $authz_file:
        ensure => file,
        owner  => 'www-data',
        mode   => 644;
      }

      # Setup the subversion repository to be accessed via http
      kbp_apache::svn_dav { "${vhost}/${name}-svn":
        ports      => $port,
        location   => "/${name}/svn",
        svnpath    => $svnrepo,
        authz      => $authz_file,
        accessfile => "/srv/www/${vhost}/${name}/htusers";
      }
    }
  } else {
    notify { "The vhost ${vhost} needs to be created.":; }
  }

  # Setup the subversion repository, if needed.
  if $svnrepo {
    kbp_subversion::repo { $name:
      svngroup => 'www-data',
      svndir   => $svnrepo;
    }
  }

  if $dbtype == 'postgres' {
    # Create user and database if the database is running on localhost
    if $dbhost == 'localhost' {
      gen_postgresql::server::user { $dbuser: password => $dbpassword; }
      gen_postgresql::server::db   { $dbname: owner    => $dbuser;     }
    } else {
      notify { 'Automatic database/user creation only implemented for postgresql on localhost for now.':; }
    }
  }

  # Warn about setting up the git repo
  if $gitrepo {
    fail('This code hasn\'t been written yet!')
  }
}

# Define: kbp_trac::accountmanager_setup
#
# Actions: Setup config and module for trac accountmanager
#
# Parameters:
#  name: The name of the trac instance.
#  path: The path to the trac instance. Defaults to '/srv/trac/$name'.
#  access_file: Location of the htaccess file for this site.
#
# Depends:
#  gen_trac
#
define kbp_trac::accountmanager_setup ($access_file, $path="/srv/trac/${name}") {
  gen_trac::accountmanager_setup { $name:
    path        => $path,
    access_file => $access_file;
  }
}

# Define: kbp_trac::datefield_setup
#
# Actions: Setup and configure the datefield plugin for a trac instance.
#
# Parameters:
#  name: The name of the trac instance.
#  path: The path to the trac instance. Defaults to '/srv/trac/$name'.
#  date_*: Settings for datefield, more info can be found at http://trac-hacks.org/wiki/DateFieldPlugin.
#
define kbp_trac::datefield_setup ($path="/srv/trac/${name}", $date_format='mdy', $date_separator='-', $date_first_day='1') {
  gen_trac::datefield_setup { $name:
    path           => $path,
    date_format    => $date_format,
    date_separator => $date_separator,
    date_first_day => $date_first_day;
  }
}

# Define: kbp_trac::tags_setup
#
# Actions: Setup and configure the tags plugin for a trac instance.
#
# Parameters:
#  name: The name of the trac instance.
#  path: The path to the trac instance. Defaults to '/srv/trac/$name'.
#
define kbp_trac::tags_setup ($path="/srv/trac/${name}") {
  gen_trac::tags_setup { $name:
    path           => $path;
  }
}

# Define: kbp_trac::customfield_setup
#
# Actions: Setup and configure the customfield plugin for a trac instance.
#
# Parameters:
#  name: The name of the trac instance.
#  path: The path to the trac instance. Defaults to '/srv/trac/$name'.
#
define kbp_trac::customfield_setup ($path="/srv/trac/${name}") {
  gen_trac::customfield_setup { $name:
    path           => $path;
  }
}
