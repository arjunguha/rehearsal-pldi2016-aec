define git::clone(   $source,
                $localtree = "/srv/git/",
                $real_name = false,
                $branch = false) {
    if $real_name {
        $_name = $real_name
    }
    else {
        $_name = $name
    }

    exec { "git_clone_exec_$localtree/$_name":
        cwd => $localtree,
        command => "git clone $source $_name",
        creates => "$localtree/$_name/.git/"
    }

    case $branch {
        false: {}
        default: {
            exec { "git_clone_checkout_$branch_$localtree/$_name":
                cwd => "$localtree/$_name",
                command => "git checkout --track -b $branch origin/$branch",
                creates => "$localtree/$_name/.git/refs/heads/$branch"
            }
        }
    }
}
