define repository::domain(  $public = false,
                            $shared = false,
                            $localtree = "/srv/git/",
                            $owner = "root",
                            $group = "root",
                            $symlink_prefix = false,
                            $recipients = false,
                            $description = false) {
    git::repository { "$name":
        public => $public,
        shared => $shared,
        localtree => "$localtree/",
        owner => "$owner",
        group => "git-$name",
        prefix => "domain",
        symlink_prefix => "$symlink_prefix",
        recipients => $recipients,
        description => "$description",
        require => Group["git-$name"]
    }

    group { "git-$name":
        ensure => present
    }

    user { "satellite-$name":
        ensure => present,
        comment => "Satellite user for domain $name",
        groups => "git-$name",
        shell => "/usr/bin/git-shell"
    }
}
