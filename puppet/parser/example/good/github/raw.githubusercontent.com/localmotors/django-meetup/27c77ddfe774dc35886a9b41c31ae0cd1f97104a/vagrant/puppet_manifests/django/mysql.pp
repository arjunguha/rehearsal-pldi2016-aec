# Set the mysql root password
$password = "password"
exec { "set mysql root password":
	require => Package["mysql-server"],
	unless => "mysqladmin -uroot -p$password status",
	command => "mysqladmin -uroot password $password",
	subscribe => Package['mysql-server'],
	refreshonly => true,
	}

# create the databases
exec { "create databases":
	require => Exec['set mysql root password'],
	command => "mysql -uroot -p$password -e 'create database django'",
	subscribe => Exec['set mysql root password'],
	refreshonly => true,
	}
