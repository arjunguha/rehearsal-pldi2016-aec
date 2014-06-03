class system::imagick {
    $neededpackages = [ "ImageMagick", "ImageMagick-devel", "ImageMagick-perl" ]
    package { $neededpackages:
      ensure => installed
    }
    exec    { "update-channels":
      command => "pear update-channels",
      path    => "/usr/local/bin:/bin:/usr/bin:/usr/local/sbin:/usr/sbin:/sbin:/home/vagrant/bin",
      require => Package['php-pear'],
      returns => [ 0, 1, '', ' ']
    } ~>
    exec    { "install imagick":
      command => "pecl install imagick",
      path    => "/usr/local/bin:/bin:/usr/bin:/usr/local/sbin:/usr/sbin:/sbin:/home/vagrant/bin",
      require => Package['php-pear'],
      returns => [ 0, 1, '', ' ']
    }
}