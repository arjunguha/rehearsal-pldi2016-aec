/*
node 'agent1' {

  file { 'a':

    path    => '/home/vagrant/dir1',
    ensure  => absent,
    # force   => true
  }


  file { 'b':

    path    => '/home/vagrant/dir1/file1',
    ensure  => present,
    content => 'Test file',
    require => File['testdir']
  }
}
*/


/*
 * 2 packages dependendency a -> b 
 * delete 'a' from its spec
 * without require
 */

node 'agent1' {

  package { 'python-oops':
    ensure => absent
  }

  package { 'python-oops-wsgi':
    ensure => installed,
    require => Package['python-oops']
  }
}
