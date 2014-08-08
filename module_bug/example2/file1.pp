file {'/tmp/file1': ensure => present}
notify {'some file created': message => 'file1 now present'}
