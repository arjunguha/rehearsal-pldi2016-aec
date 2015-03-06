class ngrok {

    file { '/opt/ngrok':
        ensure => directory
    }

    file { '/opt/ngrok/ngrok':
        ensure => file,
        owner => root,
        group => root,
        source => 'puppet:///modules/ngrok/ngrok',
        require => File['/opt/ngrok']
    }

    file { '/usr/local/bin/ngrok':
        ensure => 'link',
        target => '/opt/ngrok/ngrok'
    }

}
