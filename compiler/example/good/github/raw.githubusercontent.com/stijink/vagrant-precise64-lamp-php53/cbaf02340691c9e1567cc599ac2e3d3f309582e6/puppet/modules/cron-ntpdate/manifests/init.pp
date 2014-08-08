class cron-ntpdate {

  # Zeit jede Stunde aktualisieren
  cron { 'cron-ntpdate':
    ensure  => present,
    command => "/usr/sbin/ntpdate ntp.ubuntu.com",
    user    => root,
    hour    => [0-23],
  }
}