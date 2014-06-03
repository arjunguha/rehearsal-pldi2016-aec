class git::client {

    #
    # Documentation on this class
    #
    # This class causes the client to gain git capabilities. Boo!
    #

    case $lsbdistcodename {
      etch: {
        os::backported_package{"git-core":
          ensure => installed
        }
      }

      default: {
        package { "git-core":
          ensure => installed
        }
      }
    }
}
