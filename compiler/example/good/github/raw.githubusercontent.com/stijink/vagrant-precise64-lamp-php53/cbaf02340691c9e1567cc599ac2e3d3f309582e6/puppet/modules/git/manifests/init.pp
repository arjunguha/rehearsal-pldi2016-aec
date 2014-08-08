class git {

  # Sicherstellen, dass git installiert ist
  package { "git":
      ensure => present,
  }
}