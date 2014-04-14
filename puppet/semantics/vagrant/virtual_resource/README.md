Puppet master/agent demo
========================

This is a demo of a virtual resources in Puppet master/agent setup.  
A virtual resource is effectively a single resource Puppet class:

- Run `vagrant up && vagrant ssh agent1`.

- Notice the file `/home/vagrant/from-master`.

- This file was created by the master, using `site.pp`.
