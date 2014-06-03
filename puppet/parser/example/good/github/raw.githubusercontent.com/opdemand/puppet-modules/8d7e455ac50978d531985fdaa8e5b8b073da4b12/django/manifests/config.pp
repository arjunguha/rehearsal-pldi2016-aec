class django::config {

  require django::params

  file {"/etc/init/django.conf":
    ensure => file,
    content => template("django/django.conf.erb"),
    require => Class[Django::Install],
  }

}