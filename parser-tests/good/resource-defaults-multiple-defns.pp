File {
  owner => "root"
}

File {
  group => "root"
}

file{"/bin": ensure => directory }
file{"/usr": ensure => directory }
