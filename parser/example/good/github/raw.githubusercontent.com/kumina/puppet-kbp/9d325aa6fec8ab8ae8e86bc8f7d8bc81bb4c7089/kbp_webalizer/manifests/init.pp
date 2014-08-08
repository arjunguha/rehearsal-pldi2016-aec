# Author: Kumina bv <support@kumina.nl>

# Class: kbp_webalizer
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_webalizer {
  include webalizer

  File <|  title == "/etc/cron.daily/webalizer" |> {
    content => template("kbp_webalizer/cron.daily/webalizer"),
  }

  file {
    "/etc/webalizer-multi.conf":
      group   => "staff",
      mode    => 755,
      content => template("kbp_webalizer/webalizer-multi.conf");
    "/usr/local/bin/webalizer-multi":
      group   => "staff",
      mode    => 755,
      content => template("kbp_webalizer/webalizer-multi");
    "/srv/www/webalizer":
      ensure  => directory;
  }

  if tagged(apache) {
    file {
      "/etc/apache2/conf.d/webalizer":
        content => template("kbp_webalizer/apache2/conf.d/webalizer"),
        require => Package["apache2"],
        notify  => Exec["reload-apache2"];
      "/var/log/apache2":
        group   => "adm",
        mode    => 755;
    }
  }
}
