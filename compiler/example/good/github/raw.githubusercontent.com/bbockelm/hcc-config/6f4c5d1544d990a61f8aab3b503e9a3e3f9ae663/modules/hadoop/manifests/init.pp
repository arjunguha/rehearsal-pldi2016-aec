#
# Class: hadoop
#

class hadoop {

	# everything should have hadoop + hadoop-libhdfs
	# as an absolute minimum

	package { "hadoop":
		#name   => "hadoop-0.20",
		name   => "hadoop",
		ensure => present,
	}

	package { "hadoop-libhdfs":
		#name   => "hadoop-0.20-libhdfs",
		name   => "hadoop-libhdfs",
		ensure => present,
	}

	package { "hadoop-client":
		name   => "hadoop-client",
      ensure => present,
	}

	# ensure /hadoop-data* directories are owned by hdfs:hadoop
	# should only do this once, but every time won't hurt
	exec { "chown hdfs:hadoop /hadoop-data*":
		path => "/usr/bin:/usr/sbin:/bin",
		onlyif => [ "test `ls -ld /hadoop-data1 | awk '{print \$3}'` != hdfs" ],
	}

	# log location owned by hadoop group and group writable
	# this should happen automatically with the newer hadoop RPMs
#	file { "/var/log/hadoop-0.20":
#		ensure => directory,
#		owner => "root", group => "hadoop", mode => 0775,
#		require => Package["hadoop"],
#	}


	# we keep our configs on a dedicated conf.red directory
	# start by cleaning and copying default configs
	file { "/etc/hadoop/conf.red":
		ensure  => directory,
		owner   => "root", group => "root", mode => 0644,
#		recurse => true,
#		purge   => true,
#		force   => true,
		source  => "puppet:///modules/hadoop/defaults",
		require => Package["hadoop"],
	}

	# now apply our custom configs
	file { "/etc/hadoop/conf.red/hdfs-site.xml":
		owner   => "root", group => "root", mode => 0644,
		content => template("hadoop/hdfs-site.xml.erb"),
		require => Package["hadoop"],
	}

	file { "/etc/hadoop/conf.red/core-site.xml":
		owner   => "root", group => "root", mode => 0644,
		content => template("hadoop/core-site.xml.erb"),
		require => Package["hadoop"],
	}

	file { "/etc/hadoop/conf.red/hadoop-metrics.properties":
		owner   => "root", group => "root", mode => 0644,
		content => template("hadoop/hadoop-metrics.properties.erb"),
		require => Package["hadoop"],
	}

	file { "/etc/hadoop/conf.red/hadoop-metrics2.properties":
		owner   => "root", group => "root", mode => 0644,
		content => template("hadoop/hadoop-metrics2.properties.erb"),
		require => Package["hadoop"],
	}

	file { "/etc/hadoop/conf.red/hadoop-env.sh":
		owner   => "root", group => "root", mode => 0644,
		content => template("hadoop/hadoop-env.sh.erb"),
		require => Package["hadoop"],
	}

	file { "/etc/hadoop/conf.red/log4j.properties":
		owner   => "root", group => "root", mode => 0644,
		content => template("hadoop/log4j.properties.erb"),
		require => Package["hadoop"],
	}

	file { "/etc/hadoop/conf.red/mapred-site.xml":
		owner   => "root", group => "root", mode => 0644,
		content => template("hadoop/mapred-site.xml.erb"),
		require => Package["hadoop"],
	}

	file {"/etc/hadoop/conf.red/rack_mapfile.txt":
		owner 	=> "root", group => "root", mode => 0644,
		source	=> "puppet:///modules/hadoop/rack_mapfile.txt",
		require => Package["hadoop"],
	}
	
	file {"/etc/hadoop/conf.red/rackmap.pl":
      owner    => "hdfs", group => "root", mode => 0744,
      source   => "puppet:///modules/hadoop/rackmap.pl",
      require => Package["hadoop"],
   }
	# ALTERNATIVES maintenance
	# we use the alternatives system to keep our hadoop configs in a dedicated
	# location called conf.red (as opposed to conf.osg from the -osg RPMs)

	# check if alternatives currently points at our configs and fix if not
	exec { "run_hadoop_conf_alt_install":
		path => "/usr/bin:/usr/sbin:/bin",
		command => "/usr/sbin/alternatives --install /etc/hadoop/conf hadoop-conf /etc/hadoop/conf.red 50", 
		unless  => "/usr/bin/test `/bin/ls -l /etc/alternatives/hadoop-conf | /bin/awk '{print \$11}'` = /etc/hadoop/conf.red",
		logoutput => true,
		require => Package["hadoop"],
	}
	exec { "run_hadoop_conf_alt_link":
		path    => "/usr/bin:/usr/sbin:/bin",
		command => "/usr/sbin/alternatives --auto hadoop-conf",
		unless  => "/usr/bin/test `/bin/ls -l /etc/alternatives/hadoop-conf | /bin/awk '{print \$11}'` = /etc/hadoop/conf.red",
		logoutput => true,
		require => Package["hadoop"],
	}



	# NOTE: Temporary fix for /usr/bin/hadoop-fuse-dfs to correctly follow symlinks
#	file { "/usr/bin/hadoop-fuse-dfs":
#		owner   => "root", group => "root", mode => 0755,
#		source  => "puppet:///modules/hadoop/hadoop-fuse-dfs",
#		require => Package["hadoop"],
#	}



	# mountsHDFS specifies whether this node needs to mount hdfs via fuse
	# if so, hadoop-fuse (which can be used without -osg) is needed
	# just require -osg special sauce for now
	# TODO: need to figure out best way to organize the -osg special sauce
	if $mountsHDFS {

		package { "hadoop-fuse":
			#name   => "hadoop-0.20-fuse",
			name   => "hadoop-hdfs-fuse",
			ensure => present,
			require => Package["hadoop"],
		}

      # EL6 nodes have SELinux on by default; install sub-package
      if $lsbmajdistrelease == "6" {

         package { "hadoop-fuse-selinux":
            #name    => "hadoop-0.20-fuse-selinux",
            name    => "hadoop-hdfs-fuse-selinux",
            ensure  => present,
            require => Package["hadoop-fuse"],
         }

      }

		# hadoop mountpoint
		file { "/mnt/hadoop": ensure => directory }
		mount { "mount_hadoop":
         name    => "/mnt/hadoop",
			device  => "hadoop-fuse-dfs",
			fstype  => "fuse",
			ensure  => mounted,
			options => "server=hadoop-name,port=9000,rdbuffer=32768,allow_other",
			atboot  => true,
			remounts => false,
			require => [ File["/mnt/hadoop"], File["/etc/hadoop/conf.red/hdfs-site.xml"], ],
		}

		require hadoop::osg
	} # mountsHDFS


	# isHDFSDatanode
	if $isHDFSDatanode {
		package { "hadoop-datanode":
			#name   => "hadoop-0.20-datanode",
			name   => "hadoop-hdfs-datanode",
			ensure => present,
			require => Package["hadoop"],
		}

		file { "hdfs-log-rotate":
			path => '/usr/local/sbin/hdfs-log-rotate',
			owner => "root", group => "root", mode => 0744,
			source   => "puppet:///modules/hadoop/hdfs-log-rotate",
			require => Package["hadoop"],
		}

		cron { "hdfs-log-rotate":
			ensure => present,
			command => '/usr/local/sbin/hdfs-log-rotate',
			user => 'root',
			minute => '45',
			hour => '4',
			require => File["hdfs-log-rotate"],
		}
	} # isHDFSDatanode
  #Limits.conf for name node.  Needed for other?

  if $isHDFSname{
	file { "limits.conf":
		path => '/etc/security/limits.conf',
	   owner => "root", group => "root", mode => 0644,
	   source => "puppet:///modules/hadoop/limits-name.conf",
		require => Package["hadoop"],
   }
   }

	file { "99-hdfs-limits.conf":
		path => "/etc/security/limits.d/99-hdfs-limits.conf",
		owner => "root", group => "root", mode => 0644,
		source => "puppet:///modules/hadoop/99-hdfs-limits.conf",
		require => Package["hadoop"],
	}
}

