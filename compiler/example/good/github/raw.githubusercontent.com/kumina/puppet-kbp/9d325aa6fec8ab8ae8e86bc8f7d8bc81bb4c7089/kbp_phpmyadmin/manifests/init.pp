# Author: Kumina bv <support@kumina.nl>

# Class: kbp_phpmyadmin
#
# Actions:
#  Setup phpmyadmin the way we want to.
#
# Depends:
#  gen_phpmyadmin
#  gen_puppet
#
class kbp_phpmyadmin {
  include gen_phpmyadmin
}

# Class: kbp_phpmyadmin::cgi
#
# Actions:
#  Setup phpmyadmin with FastCGI the way we want to.
#
# Depends:
#  gen_phpmyadmin
#  gen_puppet
#
class kbp_phpmyadmin::cgi {
  include gen_phpmyadmin::cgi
}

