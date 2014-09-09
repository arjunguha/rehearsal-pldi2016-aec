class desktop_packages {
    $desktop_packages = [
        'awesome',
        'awesome-extra',
        'xlockmore',
        'keynav',

        'calibre',
        'get-iplayer',
        'mplayer',
        'scrot',
        'youtube-dl',

        'chromium-browser',
        'firefox',
        'flashplugin-installer',

        'picard',

        'ecryptfs-utils',

        'github-backup'
    ]

    package { $desktop_packages:
        ensure => installed,
    }
}
