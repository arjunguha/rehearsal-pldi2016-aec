class nodejs {

	exec { 'add_node_repo':
    	command => '/usr/bin/add-apt-repository ppa:chris-lea/node.js'
    }

    exec { 'update_node_repo':
        command => '/usr/bin/apt-get update',
        require => Exec['add_node_repo']
    }

    $packages = [ 'nodejs' ]
    package { $packages: 
        ensure => latest,
        require => Exec['update_node_repo'],
    }

} 
