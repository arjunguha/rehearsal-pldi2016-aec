
node 'red-man.unl.edu' {

    class { 'puppetdb':
        listen_address => 'red-man.unl.edu',
    }

    class { 'puppetdb::master::config': }

}

