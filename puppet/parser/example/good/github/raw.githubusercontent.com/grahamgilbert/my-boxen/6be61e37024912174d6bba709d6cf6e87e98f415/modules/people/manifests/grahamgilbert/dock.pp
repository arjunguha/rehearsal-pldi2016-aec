class people::grahamgilbert::dock (
    $my_homedir   = $people::grahamgilbert::params::my_homedir,
    $my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
    $my_username  = $people::grahamgilbert::params::my_username
    ){

    include dockutil

    dockutil::item { 'add chrome':
        item     => "/Applications/Google Chrome.app",
        label    => "Google Chrome",
        position => 1,
        action   => "add",
        require  => Class['chrome'],
    }
    
    # dockutil::item { 'add Safari':
    #     item     => "/Applications/Safari.app",
    #     label    => "Safari",
    #     position => 1,
    #     action   => "add",
    #     # require  => Class['chrome'],
    # }
    
    dockutil::item { 'Add iTerm':
        item     => "/Applications/iTerm.app",
        label    => "iTerm",
        action   => "add",
        position => 2,
        require  => Class['iterm2::dev'],
    }
    
    dockutil::item { 'Textmate2':
        item     => "/Applications/Textmate.app",
        label    => "TextMate",
        position => 3,
        action   => "add",
        require  => Class['textmate::textmate2::release'],
    }

    dockutil::item { 'Tweetbot':
        item     => "/Applications/Tweetbot.app",
        label    => "Tweetbot",
        position => 4,
        action   => "add",
    }
    
    dockutil::item { 'IRC Cloud':
        item     => "/Users/${::luser}/Dropbox/Config/Fluid/IRC Cloud.app",
        label    => "IRC Cloud",
        position => 5,
        action   => "add",
        require  => Class['fluid'],
    }
    
    dockutil::item { 'Slack':
        item     => "/Applications/Slack.app",
        label    => "Slack",
        position => 6,
        action   => "add",
    }
	
    dockutil::item { 'VMWare':
        item     => "/Applications/VMware Fusion.app",
        label    => "VMware Fusion",
        position => 7,
        action   => "add",
    }
        
    dockutil::item { 'Gitbox':
        item     => "/Applications/Gitbox.app",
        label    => "Gitbox",
        position => 8,
        action   => "add",
    }
    
    dockutil::item { 'GitHub':
        item     => "/Applications/GitHub.app",
        label    => "GitHub",
        position => 9,
        action   => "add",
        require  => Package['Github for Mac'],
    }
    
    ## Remove the default crap    
    dockutil::item { 'Remove Launchpad':
        item   => "/Applications/Launchpad.app",
        label  => "Launchpad",
        action => "remove",
    }
    
    dockutil::item { 'Remove Mission Control':
        item   => "/Applications/Mission Control.app",
        label  => "Mission Control",
        action => "remove",
    }
    
    dockutil::item { 'Remove Safari':
        item   => "/Applications/Safari.app",
        label  => "Safari",
        action => "remove",
    }
    
    dockutil::item { 'Remove Mail':
        item   => "/Applications/Mail.app",
        label  => "Mail",
        action => "remove",
    }
    
    dockutil::item { 'Remove Contacts':
        item   => "/Applications/Contacts.app",
        label  => "Contacts",
        action => "remove",
    }
    
    dockutil::item { 'Remove Calendar':
        item   => "/Applications/Calendar.app",
        label  => "Calendar",
        action => "remove",
    }
    
    dockutil::item { 'Remove Reminders':
        item   => "/Applications/Reminders.app",
        label  => "Reminders",
        action => "remove",
    }
    
    dockutil::item { 'Remove Notes':
        item   => "/Applications/Notes.app",
        label  => "Notes",
        action => "remove",
    }
    
    dockutil::item { 'Remove Messages':
        item   => "/Applications/Messages.app",
        label  => "Messages",
        action => "remove",
    }
    
    dockutil::item { 'Remove FaceTime':
        item   => "/Applications/FaceTime.app",
        label  => "FaceTime",
        action => "remove",
    }
    
    dockutil::item { 'Remove Photo Booth':
        item   => "/Applications/Photo Booth.app",
        label  => "Photo Booth",
        action => "remove",
    }
    
    dockutil::item { 'Remove iTunes':
        item   => "/Applications/iTunes.app",
        label  => "iTunes",
        action => "remove",
    }
    
    dockutil::item { 'Remove App Store':
        item   => "/Applications/App Store.app",
        label  => "App Store",
        action => "remove",
    }
    
    dockutil::item { 'Remove System Preferences':
        item   => "/Applications/System Preferences.app",
        label  => "System Preferences",
        action => "remove",
    }
        
    dockutil::item { 'Remove iPhoto':
        item   => "/Applications/iPhoto.app",
        label  => "iPhoto",
        action => "remove",
    }
    
    dockutil::item { 'Remove Maps':
        item   => "/Applications/Maps.app",
        label  => "Maps",
        action => "remove",
    }
    
    dockutil::item { 'Remove iBooks':
        item   => "/Applications/iBooks.app",
        label  => "iBooks",
        action => "remove",
    }
}