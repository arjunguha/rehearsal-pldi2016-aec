# Class: pe_demo
# This class simply declares some user resources and declares the host class.
class pe_demo {

    # Create random users
    pe_demo::live_management::user { [ 'Arnoldo',
                                       'Giselle',
                                       'Javier',
                                       'Russel',
                                       'Milford'
                                     ]:
    }

    # Create a host entry
    include pe_demo::live_management::host

}
