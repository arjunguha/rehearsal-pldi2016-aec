# Custom project class. Use this to adapt the module to your project.
# Use puppet::red::client and puppet::red::server to client or server specific customization
# Place here only common customization you want on both roles
class puppet::red {

    # gemrc with proxy settings for seamleass gem usage
#    file { "gemrc":
#        path => "/etc/gemrc",
#        content => template("puppet/red/gemrc.erb"),
#    }
}
