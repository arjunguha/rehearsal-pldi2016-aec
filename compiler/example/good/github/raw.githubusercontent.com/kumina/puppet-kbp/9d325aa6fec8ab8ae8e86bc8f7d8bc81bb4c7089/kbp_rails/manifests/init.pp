# Class: kbp_rails::mysql
#
# Actions:
#       Set up rails with mysql backend
#
# Depends:
#  gen_base
#       gen_puppet
#
class kbp_rails::mysql {
  include gen_base::rails
  include gen_base::libmysql-ruby
}
