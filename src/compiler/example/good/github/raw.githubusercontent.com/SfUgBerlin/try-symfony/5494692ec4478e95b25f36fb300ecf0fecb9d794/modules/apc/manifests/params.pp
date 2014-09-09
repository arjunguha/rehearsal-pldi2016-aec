class apc::params {

    $pkg = $operatingsystem ? {
        /Debian|Ubuntu/ => 'php-apc',
    }
    
    #Note: apc does not macke much sense without php installed 
    $php = $operatingsystem ? {
        /Debian|Ubuntu/ => 'php5-cli',
    } 

    $conf = $operatingsystem ? {
        /Debian|Ubuntu/ => '/etc/php5/apache2/conf.d',
    }
    
    $shmsize = 256M
    
    $shmsegments = 1
    
    $ttl = 3600
}
