class laravel (
    $project = 'laravel.dev',
    $webserver = 'nginx'
) {

    $cfg_path = $webserver ? {
        'nginx'   => '/etc/nginx',
        'apache2' => '/etc/apache2',
    }


    $default_page = $webserver ? {
        'nginx'   => 'default',
        'apache2' => '000-default',
    }


    exec {
        "Install-Laravel":
            cwd     => "/var/www",
            command => "composer create-project laravel/laravel $project --prefer-dist",
            timeout => 0,
            creates => "/var/www/$project/vendor",
            require => Exec['install-composer']
    }
}
