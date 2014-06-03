class curl {

  # Sicherstellen, dass curl installiert ist
  package { "curl":
      ensure => present,
  }
}