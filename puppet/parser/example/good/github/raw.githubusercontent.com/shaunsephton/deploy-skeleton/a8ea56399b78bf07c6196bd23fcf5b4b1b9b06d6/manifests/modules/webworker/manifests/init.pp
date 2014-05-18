class webworker($base_path, $app_name, $app_module_name, $repo_url) {
    $app_path = "$base_path/$app_name"
    $app_module_path = "$base_path/$app_name/$app_module_name"

    file {
        "/etc/nginx/sites-enabled/$app_name.conf":
            ensure => present,
            owner => root,
            group => root,
            mode => 0644,
            require => Package['nginx'],
            notify => Service['nginx'],
            content => template("webworker/nginx.cfg");
        "/etc/supervisor/conf.d/$app_name.conf":
            ensure => present,
            owner => root,
            group => root,
            mode => 0644,
            require => Package['supervisor'],
            notify => Service['supervisor'],
            content => template("webworker/supervisord.conf");
        "ubuntu_ssh_dir":
            path => '/home/ubuntu/.ssh',
            ensure => directory,
            owner => ubuntu,
            group => ubuntu,
            require => User['ubuntu'];
        "ubuntu_id_rsa":
            path => "/home/ubuntu/.ssh/${app_name}_deploy_key_id_rsa",
            ensure => present,
            owner => ubuntu,
            group => ubuntu,
            mode => 0600,
            require => [ User['ubuntu'], File['ubuntu_ssh_dir'], ],
            source => 'puppet:///modules/webworker/deploy_key_id_rsa';
        "ubuntu_id_rsa.pub":
            path => "/home/ubuntu/.ssh/${app_name}_deploy_key_id_rsa.pub",
            ensure => present,
            owner => ubuntu,
            group => ubuntu,
            mode => 0644,
            require => [ User['ubuntu'], File['ubuntu_ssh_dir'], ],
            source => 'puppet:///modules/webworker/deploy_key_id_rsa.pub';
        "ubuntu_known_hosts":
            path => '/home/ubuntu/.ssh/known_hosts',
            ensure => present,
            owner => ubuntu,
            group => ubuntu,
            mode => 0644,
            require => [ User['ubuntu'], File['ubuntu_ssh_dir'], ],
            source => 'puppet:///modules/webworker/known_hosts';
        "ubuntu_gitconfig":
            path => '/home/ubuntu/.gitconfig',
            ensure => present,
            owner => ubuntu,
            group => ubuntu,
            mode => 0644,
            require => User['ubuntu'],
            source => 'puppet:///modules/webworker/gitconfig';
    }

    exec {
        "clone_repo":
            command => "/bin/sh -c \"export GIT_SSH=/home/ubuntu/${app_name}_git.sh && git clone $repo_url $app_name\"",
            cwd => "$base_path",
            unless => "test -d $app_path",
            require => [
                Package['git-core'],
                File["base_path", 'ubuntu_id_rsa', 'ubuntu_id_rsa.pub', 'ubuntu_known_hosts'],
            ];
        "update_repo":
            command => "/bin/sh -c \"export GIT_SSH=/home/ubuntu/${app_name}_git.sh && git pull origin master\"",
            cwd => "$app_path",
            require => Exec['clone_repo'];
        "create_virtualenv":
            command => 'virtualenv --no-site-packages ve',
            cwd => "$app_path",
            unless => "test -d $app_path/ve",
            require => [
                Package['libpq-dev'],
                Package['python-dev'],
                Package['python-virtualenv'],
                Exec['clone_repo'],
            ];
        "install_packages":
            command => '/bin/sh -c ". ve/bin/activate && pip install -r requirements.pip && deactivate"',
            cwd => "$app_path",
            require => Exec['create_virtualenv', 'update_repo'],
            timeout => 0,
            notify => Service['supervisor'],
    }
}