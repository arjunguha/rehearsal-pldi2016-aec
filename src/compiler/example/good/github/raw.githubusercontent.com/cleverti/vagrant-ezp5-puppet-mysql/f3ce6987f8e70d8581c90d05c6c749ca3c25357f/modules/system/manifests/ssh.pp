class system::ssh {
    exec { "ssh-keygen":
        command => "ssh-keygen -f /home/vagrant/.ssh/id_rsa -N ''",
        path => "/usr/bin:/usr/sbin:/bin:/usr/local/bin",
        refreshonly => true,
        returns => [ 0, 1, 2, '', ' ']
    }
}