# Author: Kumina bv <support@kumina.nl>

# Class: kbp_subversion::client
#
# Actions: Setup the subversion client. This currently only installs the subversion package.
#
class kbp_subversion::client {
  include gen_subversion::client
}

# Define: kbp_subversion::repo
#
# Actions: Setup a subversion repository.
#
define kbp_subversion::repo ($svndir="/srv/svn/${name}",$svngroup,$svnowner='root') {
  gen_subversion::repo { $name:
    group    => $svngroup,
    svndir   => $svndir,
    svnowner => $svnowner;
  }
}
