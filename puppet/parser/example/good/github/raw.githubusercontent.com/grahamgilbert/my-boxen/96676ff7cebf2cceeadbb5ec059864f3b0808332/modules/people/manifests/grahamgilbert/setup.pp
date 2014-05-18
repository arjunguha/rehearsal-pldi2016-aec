class people::grahamgilbert::setup {

    file {"/Users/${::luser}/src":
        ensure => link,
        target => "/Users/${::luser}/Dropbox/src"
    }

}