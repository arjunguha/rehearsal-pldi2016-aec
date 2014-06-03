# Author: Kumina bv <support@kumina.nl>

# Class: kbp_amavis
#
# Actions:
#  Set up Amavis
#
# Depends:
#  gen_amavis
#  kbp_spamassassin
#  kbp_clamav
#  gen_puppet
#
class kbp_amavis {
  include gen_amavis
  include kbp_spamassassin
  include kbp_clamav

  file {
    '/srv/spam':
      ensure  => directory,
      owner   => 'mail',
      group   => 'amavis',
      mode    => 770,
      require => Package['amavisd-new'];
    '/srv/spam/messages':
      ensure  => directory,
      owner   => 'mail',
      group   => 'amavis',
      mode    => 770;
    '/etc/cron.daily/mailclean':
      content => template('kbp_amavis/mailclean'),
      mode    => 755;
    '/etc/amavis/conf.d/40-kbp':
      content => template('kbp_amavis/40-kbp'),
      require => Package['amavisd-new'],
      notify  => Exec['reload-amavis'];
  }

  gen_munin::client::plugin { ['amavis_time', 'amavis_cache', 'amavis_content']:
    script      => 'amavis_',
    script_path => '/usr/local/share/munin/plugins';
  }

  gen_munin::client::plugin::config { 'amavis_':
    section => 'amavis_*',
    content => 'env.amavis_db_home /var/lib/amavis/db\nuser amavis';
  }
}
