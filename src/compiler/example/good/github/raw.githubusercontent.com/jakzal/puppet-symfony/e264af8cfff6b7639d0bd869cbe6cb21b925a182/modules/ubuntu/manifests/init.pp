class ubuntu {
    exec { 'apt-get-update':
        path => '/usr/bin',
        command => 'apt-get update'
    }
}
