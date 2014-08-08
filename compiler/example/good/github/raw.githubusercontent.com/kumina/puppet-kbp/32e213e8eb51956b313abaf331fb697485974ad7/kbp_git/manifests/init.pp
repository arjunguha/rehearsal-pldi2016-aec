# Author: Kumina bv <support@kumina.nl>

# Class: kbp_git
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_git {
  include gen_git
}

# Define: kbp_git::repo
#
# Actions:
#  Set up git repository
#
# Parameters:
#  name
#    The directory where to create the repository.
#    Needs to be a kfile already.
#  branch
#    The remote branch of the origin. Defaults to
#    "master".
#  origin
#    Add an origin to the repository. This does
#    not clone the remote repository.
#  bare
#    Should the repository be 'bare'
#  post_update_src
#    The source for a post_update hook script
#
# Depends:
#  kbp_git
#  gen_git::repo
#  gen_puppet
#
define kbp_git::repo ($branch = "master", $origin = false, $bare = false, $post_update_content = false) {
  include kbp_git

  gen_git::repo { $name:
    branch              => $branch,
    origin              => $origin,
    bare                => $bare,
    post_update_content => $post_update_content;
  }
}
