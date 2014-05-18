# Class: kbp_spamassassin
#
# Actions:
#  Set up SpamAssassin
#
# Depends:
#  gen_base
#  gen_puppet
#
class kbp_spamassassin {
  include gen_spamassassin
  # Pyzor and Razor work similarly (they both use checksums for detecting spam), but the details differ. http://spamassassinbook.packtpub.com/chapter11.htm has a good description on the differences.
  include gen_base::pyzor
  include gen_base::razor

  file { '/etc/spamassassin/local.cf':
    content => template('kbp_spamassassin/local.cf'),
    notify  => Exec['reload-amavis'],
    require => Package["spamassassin"];
  }
}
