define tcpwrappers::entry($ensure = present,
                          $type,
                          $daemon,
                          $client,
                          $except = undef) {
	include tcpwrappers::lens

	case $type {
		allow,deny: {}
		default: { fail("Invalid type: ${type}") }
	}

	Augeas {
		incl    => "/etc/hosts.${type}",
		lens    => "Tcpwrappers.lns",
		require => File["/usr/share/augeas/lenses/tcpwrappers.aug"],
	}

	if $daemon =~ /^(?:\w[\w.-]*\w|\w)$/ {
		$daemon_ = $daemon
	} else {
		fail("Invalid daemon: ${daemon}")
	}
	$client_ = normalize_tcpwrappers_client($client)
	if $except {
		$except_ = normalize_tcpwrappers_client($except)
	} else {
		$except_ = undef
	}

	# Only look at an entry with a single daemon and no daemon exceptions.
	$entry = "entry[count(daemons/daemon)=1][daemons/daemon='${daemon_}'][count(daemons/except/daemon)=0]"

	if $except_ {
		$key = "tcpwrappers/allow/${daemon_}:${client_}:${except_}"
	} else {
		$key = "tcpwrappers/allow/${daemon_}:${client_}"
	}

	case $ensure {
		present: {
			# If the new item is to be added with no client
			# exception, start by removing the client from
			# any entry where it appears with an exception
			# list.
			if $except_ {
			} else {
				augeas { "${key}/cleanup":
					changes => [
						"rm ${entry}/clients/client[.='${client_}']",
						"rm ${entry}[count(clients/client)=0]",
					],
					onlyif  => "match ${entry}/clients/client[.='${client_}'][../except/client] size > 0",
					before  => Augeas["${key}/new"];
				}
			}

			# Next, either add the key entry from scratch, or
			# modify the key entry to contain the client.
			#
			# The key entry is the one that has a client
			# exception list matching this resource.
			if $except_ {
				$key_entry = "${entry}[count(clients/except/client)=1][clients/except/client='$except_']"
			} else {
				$key_entry = "${entry}[count(clients/except/client)=0]"
			}

			$create_cmds = [
				"clear entry[0]",
				"set entry[last()]/daemons/daemon '${daemon_}'",
				"set entry[last()]/clients/client '${client_}'",
			]
			if $except_ {
				$extra_create_cmds = [ "set entry[last()]/clients/except/client '${except_}'" ]
			} else {
				$extra_create_cmds = []
			}

			augeas {
				"${key}/new":
					# Use stdlib, see https://github.com/anchor/puppet-module-tcpwrappers/issues/1
					#changes => sum($create_cmds, $extra_create_cmds),
					changes => flatten([$create_cmds, $extra_create_cmds]),
					onlyif  => "match ${key_entry} size == 0";
				$key:
					changes => "set ${key_entry}/clients/client[.='${client_}'] '${client_}'",
					onlyif  => "match ${key_entry}/clients/client[.='${client_}'] size == 0",
					require => Augeas["${key}/new"];
			}
		}
		absent: {
			# If this resource is not given a client exception,
			# remove the client from all entries, otherwise find
			# the entry with a matching client exception list.
			if $except_ {
				$key_entry = "${entry}[count(clients/except/client)=1][clients/except/client='$except_']"
			} else {
				$key_entry = $entry
			}

			augeas { $key:
				changes => [
					"rm ${key_entry}/clients/client[.='${client_}']",
					"rm ${entry}[count(clients/client)=0]",
				],
				onlyif  => "match ${key_entry}/clients/client[.='${client_}'] size > 0";
			}
		}
		default: { fail("Invalid ensure: ${ensure}") }
	}
}
