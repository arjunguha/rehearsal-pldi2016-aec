class tcpwrappers::lens {
	file { "/usr/share/augeas/lenses/tcpwrappers.aug":
		source => "puppet:///modules/tcpwrappers/usr/share/augeas/lenses/tcpwrappers.aug",
		mode   => 0444;
	}
}
