# Class: openssh::red
#
# Custom class for module openssh on the red project. Here you should define all your custom behaviours of the module openssh
# For best reusability (on different projects) place here, whenever possible, all your customizations of this module.
#
# Usage:
# This class doesn't need to be called directly. It's automatically included by class openssh if you have the $my_project varble set as "red"
#
# Notes: 
# There are basically TWO different ways to "instance" this class:
# class openssh::red { } - Without inheritance. Use this method if the class just adds resources ot the ones managed in the main openssh class
# class openssh::red inherits openssh { } - WITH inheritance. Use this method if you need to override parameters of resources already defined in the main openssh class.
# The latter method is useful, for example, to provide configuration files according to custom logic.
#
class openssh::red inherits openssh {

	File["sshd_config"] {
#		content => $lsbmajdistrelease ? {
#			6 => [ template("openssh/sshd_config-$hostname.erb"), template("openssh/sshd_config-rhel6.erb"), ],
#			default => [ template("openssh/sshd_config-$hostname.erb"), template("openssh/sshd_config.erb"), ],
#		}

		content => $lsbmajdistrelease ? {
			6 => inline_template(file("/etc/puppet/modules/openssh/templates/sshd_config-$hostname.erb", "/etc/puppet/modules/openssh/templates/sshd_config-rhel6.erb")),
			default => inline_template(file("/etc/puppet/modules/openssh/templates/sshd_config-$hostname.erb", "/etc/puppet/modules/openssh/templates/sshd_config.erb")),
		}
	}


#    File["sshd_config"] {
#        source => [ 
#            "${openssh::params::openssh_source}/red/sshd_config-$hostname",
#            "${openssh::params::openssh_source}/red/sshd_config-$role",
#            "${openssh::params::openssh_source}/red/sshd_config",
#        ],
#    }

}
