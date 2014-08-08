class people::grahamgilbert::files {

    file {"/Users/${::luser}/src/Mine":
        ensure => link,
        target => "/Users/${::luser}/Dropbox/src/Mine",
    }
    
    file {"/Users/${::luser}/src/Others":
        ensure => link,
        target => "/Users/${::luser}/Dropbox/src/Others",
    }

    file {"/Users/${::luser}/src/Work":
        ensure => link,
        target => "/Users/${::luser}/Dropbox/src/Work",
    }
}