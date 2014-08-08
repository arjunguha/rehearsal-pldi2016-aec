# Class: kbp_rvm
#
# Actions: Sets up all dependencies for rvm.
#
class kbp_rvm {
  include gen_base::autoconf
  include gen_base::automake
  include gen_base::bison
  include gen_base::build_essential
  include gen_base::curl
  include gen_base::libc6_dev
  include gen_base::libsqlite3_dev
  include gen_base::libreadline6
  include gen_base::libreadline6_dev
  include gen_base::libssl-dev
  include gen_base::libtool
  include gen_base::libxml2_dev
  include gen_base::libxslt1_1
  include gen_base::libxslt1_dev
  include gen_base::libyaml_dev
  include gen_base::ncurses_dev
  include gen_base::sqlite3
  include gen_base::zlib1g
  include gen_base::zlib1g_dev
  include gen_git
  include gen_openssl::common
  include gen_subversion::client
  include gen_base::libgdbm_dev
  include gen_base::libffi_dev
}
