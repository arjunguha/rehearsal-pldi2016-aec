# /etc/puppet/manifests/site.pp

import "nodes"

# The filebucket option allows for file backups to the server

filebucket { main:
  server => 'puppet';
}

# Set global defaults - including backing up all files to the main filebucket
# and adds a global path

File { backup => main }

case $operatingsystem {
  Solaris: {
    Package { provider => pkg }
  }
}

Exec { path => "/usr/sbin:/usr/bin/:/sbin:/bin" }

# site.pp ends here
