# selinuxmodules
# Manage SELinux policies using just the .te rules
# created by audit2allow
# Create .te files via something like:
# cat /var/log/audit/audit.log | grep nrpe | grep denied | audit2allow -m nrpe_sssd > nrpe_sssd.te

class selinuxmodules {

file {
		"/etc/selinux/mymodules":
		ensure => directory,
		mode => 600;
	  }
file {
		"/usr/bin/compile_selinux.sh":
		source => "puppet:///modules/selinuxmodules/compile_selinux.sh",
		mode => 755,
		require => File["/etc/selinux/mymodules"];
}

exec {
		"repackage-semods":
		command => "/usr/bin/compile_selinux.sh",
		cwd => "/tmp/",
		refreshonly=>true;
} 

define myselmod()
{
		file {$name:
				owner => root,
				group => root,
				mode => 600,
				path => "/etc/selinux/mymodules/${name}",
				notify => Exec["repackage-semods"],
				require => File["/etc/selinux/mymodules"],
				source => "puppet:///modules/selinuxmodules/${name}";
		}
} 

myselmod {"nrpe_sssd.te": } 
myselmod {"node_health.te":}
}
