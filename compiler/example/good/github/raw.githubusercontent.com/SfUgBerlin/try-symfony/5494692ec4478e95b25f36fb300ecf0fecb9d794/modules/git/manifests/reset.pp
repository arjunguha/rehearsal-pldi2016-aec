define git::reset($localtree = "/srv/git/", $real_name = false, $clean = true) {

    #
    # Resource to reset changes in a working directory
    # Useful to undo any changes that might have occured in directories
    # that you want to pull for. This resource is automatically called
    # with every pull by default.
    #
    # You can set $clean to false to prevent a clean (removing untracked
    # files)
    #

    exec { "git_reset_exec_$name":
        cwd => $real_name ? {
            false => "$localtree/$name",
            default => "$localtree/$real_name"
        },
        command => "git reset --hard HEAD"
    }

    if $clean {
        git::clean { "$name":
            localtree => "$localtree",
            real_name => "$real_name"
        }
    }
}
