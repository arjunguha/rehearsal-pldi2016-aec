class php::tools::composer {
    exec { 'install-composer':
        command => 'curl -s https://getcomposer.org/installer | php && mv composer.phar /usr/local/bin/composer && chmod +x /usr/local/bin/composer',
        require => Package[ 'php5-cli', 'curl'],
        creates => '/usr/local/bin/composer';
    }
}