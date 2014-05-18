class nodejs {
	package { 'nodejs':
		ensure => present,
	}

	exec {'install npm':
		command => 'curl http://npmjs.org/install.sh | clean=yes sh',
		creates => '/usr/local/bin/npm',
		group => root,
		path => [
			'/usr/bin',
			'/usr/local/bin',
			'/bin'
		],
		user => root,

		require => [
			Package['curl'],
			Package['nodejs']
		]
	}

	define installNpmPackage ($creates) {
		# $name refers to package name
		exec {"npm install -g $name":
			creates => $creates,
			group => root,
			path => [
				'/bin',
				'/usr/bin',
				'/usr/local/bin'
			],
			user => root,

			require => [
				Exec['install npm'],
			]
		}
	}

	installNpmPackage {'coffee-script':
		creates => '/usr/local/bin/coffee',
	}

	installNpmPackage {'less':
		creates => '/usr/local/bin/lessc',
	}

	installNpmPackage {'uglify-js':
		creates => '/usr/local/bin/uglifyjs',
	}
}