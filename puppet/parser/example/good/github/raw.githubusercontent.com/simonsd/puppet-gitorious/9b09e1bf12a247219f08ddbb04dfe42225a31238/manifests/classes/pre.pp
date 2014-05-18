class gitorious::pre {
    @exec {
		'gem update system':
			command => 'gem update --system;gem update --system 1.5.3',
			onlyif => 'which gem',
			provider => 'shell',
			unless => '[[ `gem -v` == "1.5.3" ]]';

		'gem update':
			command => 'gem update',
			onlyif => 'which gem',
			require => Exec['gem update system'];

		'apt update':
			command => 'apt-get update';

		'yum update':
	        command => "yum -y update",
	        cwd => "/root/",
	        refreshonly => true,
	        timeout => 20000;

		remove_32:
			command => 'sudo yum -y remove *.i*86',
			onlyif => "yum list installed|grep '.i.86'";
	}

	if $::operatingsystem == 'Centos' {
		realize(Exec['yum update', 'remove_32'])
	} else {
		realize(Exec['apt update'])
	}

	realize(Exec['gem update system'])
}
