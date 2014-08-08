/*

Class: git-subtree

Installs git-subtree and adds a symlink to /usr/local/bin

*/
class git-subtree {

  if ($::git_version) {
    if (versioncmp('1.7.0', $::git_version) >= 0) {
      fail 'git-subtree requires git 1.7 or later!'
    } else {
      vcsrepo { '/usr/src/git-subtree':
        ensure   => present,
        source   => 'http://github.com/apenwarr/git-subtree.git',
        provider => 'git',
        revision => '2793ee6ba',
      }

      file { '/usr/local/bin/git-subtree':
        ensure  => file,
        source  => 'file:///usr/src/git-subtree/git-subtree.sh',
        owner   => 'root',
        mode    => '0755',
        require => Vcsrepo['/usr/src/git-subtree'],
      }

      file { '/etc/bash_completion.d/git-subtree':
        ensure => file,
        # Use /usr/src once PR 12 is merged by upstream
        source => 'puppet:///modules/git-subtree/bash_completion.sh',
        mode   => '0644',
      }
    }
  } else {
    warning 'You need to install git before you can use the git-subtree class'
  }
}
