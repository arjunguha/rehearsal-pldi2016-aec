define mysql2::database (
   $username = undef,
   $password = undef
){
    include mysql2::settings

    exec {
        "create-${name}":
            unless      => "mysql ${name}",
            command     => "mysql -e \"create database ${name}\"",
            path        => ["/bin", "/usr/bin", "/usr/local/bin"],
            environment => ['HOME=/root'],
            require     => Service[$mysql2::settings::service_name],
    }

    if $username != undef and $password != undef {
        mysql2::grant {
            $name:
                username => $username,
                password => $password,
                database => $name;
        }
    }
}
