define git::repository(  $public = false, $shared = false,
                    $localtree = "/srv/git/", $owner = "root",
                    $group = "root", $symlink_prefix = false,
                    $prefix = false, $recipients = false,
                    $description = false) {
    # FIXME
    # Why does this include server? One can run repositories without a
    # git daemon..!!
    #
    # - The defined File["git_init_script"] resource will need to move to
    # this class
    #
    # Documentation on this resource
    #
    # Set $public to true when calling this resource to make the repository
    # readable to others
    #
    # Set $shared to true to allow the group owner (set with $group) to
    # write to the repository
    #
    # Set $localtree to the base directory of where you would like to have
    # the git repository located.
    #
    # The actual git repository would end up in $localtree/$name, where
    # $name is the title you gave to the resource.
    #
    # Set $owner to the user that is the owner of the entire git repository
    #
    # Set $group to the group that is the owner of the entire git repository
    #
    # Set $init to false to prevent the initial commit to be made
    #

    include git::server

    file { "git_repository_$name":
        path => $prefix ? {
            false => "$localtree/$name",
            default => "$localtree/$prefix-$name"
        },
        ensure => directory,
        owner => "$owner",
        group => "$group",
        mode => $public ? {
            true => $shared ? {
                true => 2775,
                default => 0755
            },
            default => $shared ? {
                true => 2770,
                default => 0750
            }
        }
    }

    # Set the hook for this repository
    file { "git_repository_hook_post-commit_$name":
        path => $prefix ? {
            false => "$localtree/$name/hooks/post-commit",
            default => "$localtree/$prefix-$name/hooks/post-commit"
        },
        source => "puppet://$server/git/post-commit",
        mode => 755,
        require => [
            File["git_repository_$name"],
            Exec["git_init_script_$name"]
        ]
    }

    file { "git_repository_hook_update_$name":
        path => $prefix ? {
            false => "$localtree/$name/hooks/update",
            default => "$localtree/$prefix-$name/hooks/update"
        },
        ensure => "$localtree/$name/hooks/post-commit",
        require => [
            File["git_repository_$name"],
            Exec["git_init_script_$name"]
        ]
    }

    file { "git_repository_hook_post-update_$name":
        path => $prefix ? {
            false => "$localtree/$name/hooks/post-update",
            default => "$localtree/$prefix-$name/hooks/post-update"
        },
        mode => 755,
        owner => "$owner",
        group => "$group",
        require => [
            File["git_repository_$name"],
            Exec["git_init_script_$name"]
        ]
    }

    # In case there are recipients defined, get in the commit-list
    case $recipients {
        false: {}
        default: {
            file { "git_repository_commit_list_$name":
                path => $prefix ? {
                    false => "$localtree/$name/commit-list",
                    default => "$localtree/$prefix-$name/commit-list"
                },
                content => template('git/commit-list.erb'),
                require => [
                    File["git_repository_$name"],
                    Exec["git_init_script_$name"]
                ]
            }
        }
    }

    case $description {
        false: {}
        default: {
            file { "git_repository_description_$name":
                path => $prefix ? {
                    false => "$localtree/$name/description",
                    default => "$localtree/$prefix-$name/description"
                },
                content => "$description",
                require => [
                    File["git_repository_$name"],
                    Exec["git_init_script_$name"]
                ]
            }
        }
    }

    exec { "git_init_script_$name":
        command => $prefix ? {
            false => "git_init_script --localtree $localtree --name $name --shared $shared --public $public --owner $owner --group $group",
            default => "git_init_script --localtree $localtree --name $prefix-$name --shared $shared --public $public --owner $owner --group $group"
        },
        creates => $prefix ? {
            false => "$localtree/$name/info",
            default => "$localtree/$prefix-$name"
        },
        require => [
            File["git_repository_$name"],
            File["/usr/local/bin/git_init_script"]
        ]
    }
}
