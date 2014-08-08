define kbp_mediawiki::site($basepath="/srv/www") {
  gen_mediawiki::site { "${basepath}/${name}":
    require => File["${basepath}/${name}"],
  }

  file { "/etc/apache2/conf.d/mediawiki.conf":
    ensure  => link,
    target  => "/etc/mediawiki/apache.conf",
    require => Package["mediawiki"],
  }
}

define kbp_mediawiki::extension($site, $basepath="/srv/www", $extrapath="base/", $linkname=$name) {
  gen_mediawiki::extension { $name:
    sitepath  => "${basepath}/${site}",
    linkname  => $linkname,
    extrapath => $extrapath,
    require   => Kbp_mediawiki::Site[$site],
  }
}
