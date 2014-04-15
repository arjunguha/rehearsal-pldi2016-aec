Puppet master/agent demo
========================

This is a demo of a resource ordering and notification in Puppet master/agent setup.  

- Run `vagrant up && vagrant ssh agent1`.

- Notice the file `/home/vagrant/src1` and its contents.

- Notice the file `/home/vagrant/src1_md5s` and its contents

- This file was created by the master, using `site.pp`.

- Run `vagrant ssh master`

- Change contents of `/home/vagrant/src1` in `/etc/puppet/manifest/site.pp`

- Run `vagrant ssh agent1`

- Run `sudo service puppet restart`

- Contents of `/home/vagrant/src1` will change and new md5s will be appended in `/vagrant/home/src1_md5s`
