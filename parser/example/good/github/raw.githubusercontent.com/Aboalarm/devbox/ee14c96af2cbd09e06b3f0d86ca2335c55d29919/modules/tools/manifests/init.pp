class tools {
    $packages = ['python-software-properties', 'curl', 'imagemagick', 'build-essential']
    
    package { $packages:
        ensure => installed,
    }
}
