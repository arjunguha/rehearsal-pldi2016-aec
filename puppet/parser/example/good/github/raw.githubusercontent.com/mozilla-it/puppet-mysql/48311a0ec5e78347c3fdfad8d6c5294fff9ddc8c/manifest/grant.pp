define mysql2::grant (
   $username,
   $password,
   $database,
   $privileges     = "ALL PRIVILEGES",
   $tables         = "*",
   $host           = "localhost",
   $grant          = undef,
   $revoke         = false
){
    include mysql2::settings

    $grantopt = $grant ? {
        undef   => "",
        default => " WITH GRANT OPTION",
    }
    
    $grantrevoke = $grant ? {
        undef   => "",
        default => ", GRANT OPTION",
    }

    if ($revoke) {
        exec{
            "mysql2::grant::${name}":
                command     => "mysql -e \"REVOKE ${privileges},${grantrevoke} ON ${database}.${tables} FROM ${username}@'${host}'; FLUSH PRIVILEGES\"",   
                onlyif      => "mysql -e \"SHOW GRANTS FOR '${username}'@'${host}'\" | tr -d \"'\\`\" | grep -i \"GRANT ${privileges} ON ${database}.${tables} TO ${username}@${host}${grantopt}\"",            
                path        => ["/bin", "/usr/bin", "/usr/local/bin"],
                environment => ['HOME=/root'],
                require     => Service[$mysql2::settings::service_name];
        }
    } else { 
        exec {
            "mysql2::grant::${name}":
                command     => "mysql -e \"GRANT ${privileges} ON ${database}.${tables} TO ${username}@'${host}' IDENTIFIED BY '${password}' ${grantopt}; FLUSH PRIVILEGES\"",
                unless      => "mysql -e \"SHOW GRANTS FOR '${username}'@'${host}'\" | tr -d \"'\\`\" | grep -i \"GRANT ${privileges} ON ${database}.${tables} TO ${username}@${host}${grantopt}\"",
            path        => ["/bin", "/usr/bin", "/usr/local/bin"],
            environment => ['HOME=/root'],
            require     => Service[$mysql2::settings::service_name]; 
        }
    }
}
