class database ($db_name, $db_username, $db_password) {
    postgres::role {
        "$db_username":
            password => "$db_password",
            ensure => present,
            require => Package['postgresql'];
    }
    postgres::database {
        "$db_name":
            owner => "$db_username",
            ensure => present,
            template => "template0",
            require => [Package['postgresql'], postgres::role["$db_username"]];
    }
}