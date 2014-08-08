class machine {
    Exec {
            path => ['/bin', '/usr/bin', '/usr/local/bin'],
            user => ubuntu,
        }

    class {
        "base":
            base_path => "$base_path";
        "database":
            db_name => "$db_name",
            db_username => "$db_username",
            db_password => "$db_password";
        "webworker":
            base_path => "$base_path",
            app_name => "$app_name",
            app_module_name => "$app_module_name",
            repo_url => "$repo_url";
    }
}