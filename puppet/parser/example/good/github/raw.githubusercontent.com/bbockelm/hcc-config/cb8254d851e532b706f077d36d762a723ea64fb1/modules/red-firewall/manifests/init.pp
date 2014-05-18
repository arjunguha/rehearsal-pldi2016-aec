class red-firewall {

	$ipv4_file = $operatingsystem ? {
		"debian" => "/etc/iptables/rules.v4",
		/(RedHat|CentOS|Scientific)/ => "/etc/sysconfig/iptables",
	}

	exec { "purge-default-firewall":
		command => "/sbin/iptables -F && /sbin/iptables-save > $ipv4_file && /sbin/service iptables restart",
		onlyif  => "/usr/bin/test `/bin/grep \"Firewall configuration written by\" $ipv4_file | /usr/bin/wc -l` -gt 0",
		user    => "root",
	}

	exec { "persist-firewall":
		command     => "/bin/echo \"# This file is managed by puppet - do not modify\" > $ipv4_file && /sbin/iptables-save >> $ipv4_file",
		refreshonly => true,
		user        => "root",
	}


	resources { 'firewall':
		purge => true,
	}

	firewall { "100 allow ssh from 239 subnet":
		state => [ 'NEW' ],
		dport => '22',
		proto => 'tcp',
		action => 'accept',
		source => '129.93.239.128/26',
	}

}
