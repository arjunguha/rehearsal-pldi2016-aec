class cron_apt {
    package { 'cron-apt':
        ensure => installed
    }

    file { '/etc/cron.daily/cron-apt':
        ensure => symlink,
        target => '/usr/sbin/cron-apt',
    }
}
