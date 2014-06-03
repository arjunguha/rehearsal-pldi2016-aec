Exec {
    path => ['/bin/', '/sbin/', '/usr/bin/', '/usr/sbin/', '/usr/local/bin']
}

File {
    owner => 0,
    group => 0,
    mode  => 0644
}

class devbox {

    group { "puppet":
        ensure => "present",
    }

    exec {
        'update-apt':
            command => 'apt-get update',
            notify  => Exec['upgrade-apt'],
            onlyif  => "bash -c 'cd /var/lib/apt/lists; exit $(( $(( $(date +%s) - $(stat -c %Y ./$( ls ./ -tr1|tail -1 )) )) <= 604800 ))'";

        'manual-update-apt':
            command =>'apt-get update',
            refreshonly => true;

        'upgrade-apt':
            command     => 'apt-get upgrade -y -q -o Dpkg::Options::=--force-confold --force-yes',
            require     => Exec['update-apt'],
            refreshonly => true;
    }

    package { [
            'build-essential',
            'ack-grep',
            'curl',
            'locate',
            'pastebinit',
            'unzip',
            'git-core',
            'xsel',
            'python-software-properties',
            'ppa-purge'
        ]:
        ensure => "installed",
        require => Exec['update-apt'];
    }
}

include devbox
include vim
include nginx
class {'php':
  version => '5.5',
}
include mysql
include phpmyadmin
include laravel