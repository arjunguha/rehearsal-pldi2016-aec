# We do not setup or maintain twiki, but this helps in setting up a vhost that can be used
# to install the application.

# Class: kbp_twiki
#
# Action:
#  Setup a twiki environment.
#
# Depends:
#  gen_twiki
#
class kbp_twiki {
  include gen_twiki
}

# Define: kbp_twiki::site
#
# Action:
#  Setup Apache to handle a twiki.
#
# Parameters:
#  name
#   The vhost that will be used for the site.
#
# Depends:
#  kbp_twiki
#  kbp_apache
#
define kbp_twiki::site ($port = "80") {
  include kbp_twiki
  include kbp_apache::module::cgid

  $vhost_directory = "/srv/www/${name}"

  kbp_apache::vhost_addition { "${name}/twiki":
    ports   => $port,
    content => template("kbp_twiki/apache.conf");
  }
}
