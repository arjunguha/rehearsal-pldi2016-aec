$pkglist = [ 'httpd', 'mod_passenger', 'mod_ssl', 'mysql-server', 'puppet-server', 'rubygems' ]

case $operatingsystemmajrelease {
    5: {
        $passenger_rpm_key = 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-passenger.rhel5'
        $pkgs = $pkglist
    }
    6: {
        $passenger_rpm_key = 'http://passenger.stealthymonkeys.com/RPM-GPG-KEY-stealthymonkeys.asc'
        $pkgs = [ $pkglist, 'puppet-dashboard' ]
    }
    default: { }
}

$vardir       = '/var/lib/puppet'
$logdir       = '/var/log/puppet'
$rundir       = '/var/run/puppet'
$ssldir       = '$confdir/ssl'
$report       = true
$puppetmaster = "puppet.${::domain}"
$ismaster     = 'yes'

File { owner => 'root', group => 'puppet', mode => '0644' }

file { 'passenger_gpg_key':
    path   => '/etc/pki/rpm-gpg/RPM-GPG-KEY-passenger.rhel5',
    group  => 'root',
    source => 'puppet:///modules/puppet-master/RPM-GPG-KEY-passenger.rhel5',
    before => Yumrepo[ 'passenger' ],
}

file {
    '/etc/puppet/hiera.yaml':
        source => 'puppet:///modules/puppet-master/hiera.yaml',
    ;
    '/etc/puppet/data':
        ensure => directory,
    ;
    '/etc/puppet/data/puppet.yaml':
        content => template ('puppet-master/puppet.yaml.erb'),
        require => File[ '/etc/puppet/data' ],
    ;
    '/etc/puppet/puppet.conf':
        content => template('puppet-master/puppet.conf.erb'),
        notify  => Service[ 'httpd' ],
    ;
    '/etc/puppet/autosign.conf':
        content => "*.${::domain}\n",
    ;
}

file { '/var/lib/puppet/reports':
    ensure => 'directory',
    owner  => 'puppet',
    group  => 'puppet',
    mode   => '0750',
}

exec { 'create_puppet_cert':
    command => 'puppet cert generate puppet.$(facter domain)',
    path    => '/usr/bin',
    creates => "/etc/puppet/ssl/certs/puppet.${::domain}.pem",
    unless  => "test -f /etc/puppet/ssl/certs/puppet.${::domain}.pem",
    require => [
        File[ '/etc/puppet/puppet.conf' ],
        Package[ 'httpd' ],
    ],
}

file { [ '/etc/puppet/ssl/private_keys',
         "/etc/puppet/ssl/certs/puppet.${::domain}.pem",
         "/etc/puppet/ssl/private_keys/puppet.${::domain}.pem" ]:
        owner   => 'puppet',
        group   => 'apache',
        mode    => '0640',
        require => Exec[ 'create_puppet_cert' ],
}

yumrepo { 'passenger':
    descr    => "Red Hat Enterprise ${::operatingsystemmajrelease} - Phusion Passenger",
    baseurl  => "http://passenger.stealthymonkeys.com/rhel/${::operatingsystemmajrelease}/\$basearch",
    enabled  => 1,
    gpgcheck => 1,
    gpgkey   => $passenger_rpm_key,
    require  => File[ 'passenger_gpg_key' ],
}

yumrepo { 'epel':
    descr      => "Extra Packages for Enterprise Linux ${::operatingsystemmajrelease} - \$basearch",
    mirrorlist => "https://mirrors.fedoraproject.org/mirrorlist?repo=epel-${::operatingsystemmajrelease}&arch=\$basearch",
    enabled    => 1,
    gpgcheck   => 1,
    gpgkey     => 'https://fedoraproject.org/static/217521F6.txt https://fedoraproject.org/static/0608B895.txt',
}

yumrepo { 'puppet':
    descr    => 'Puppetlabs',
    baseurl  => "http://yum.puppetlabs.com/el/${::operatingsystemmajrelease}/products/\$basearch",
    enabled  => 1,
    gpgcheck => 1,
    gpgkey   => 'http://yum.puppetlabs.com/RPM-GPG-KEY-puppetlabs http://yum.puppetlabs.com/RPM-GPG-KEY-reductive',
}

yumrepo { 'puppet-deps':
    descr    => 'Puppetlabs dependencies',
    baseurl  => "http://yum.puppetlabs.com/el/${::operatingsystemmajrelease}/dependencies/\$basearch",
    enabled  => 1,
    gpgcheck => 1,
    gpgkey   => 'http://yum.puppetlabs.com/RPM-GPG-KEY-puppetlabs http://yum.puppetlabs.com/RPM-GPG-KEY-reductive',
}

package { $pkgs:
    ensure  => installed,
    require => Yumrepo[ [ 'epel', 'passenger', 'puppet' ] ],
}

package { [ 'hiera', 'hiera-puppet' ]:
    ensure   => installed,
    provider => 'gem',
    require  => Package[ 'rubygems' ],
}

file { [ '/etc/puppet/rack', '/etc/puppet/rack/public' ]:
    ensure => directory,
    owner  => 'root',
    group  => 'root',
    mode   => '0755',
}

file { '/etc/puppet/rack/config.ru':
    ensure  => present,
    source  => 'puppet:///modules/puppet-master/config.ru',
    owner   => 'puppet',
    group   => 'root',
    mode    => '0644',
    require => File[ '/etc/puppet/rack' ],
}

file { '/etc/httpd/conf.d/puppetmaster.conf':
    ensure  => present,
    content => template('puppet-master/puppetmaster.conf.erb'),
    owner   => 'root',
    group   => 'root',
    mode    => '0644',
    require => [
        File[ [ '/etc/puppet/rack/config.ru', '/etc/puppet/rack/public' ] ],
        Package[ 'httpd' ],
    ],
    notify  => Service[ 'httpd' ],
}

service { 'httpd':
    ensure  => running,
    enable  => true,
    require => Package[ 'httpd' ],
}

service { 'puppetmaster':
    ensure => stopped,
    enable => false,
}

service { 'mysqld':
    ensure  => running,
    enable  => true,
    require => Package[ 'mysql-server' ],
}

# vim: set ts=4 sw=4 et syn=puppet:
