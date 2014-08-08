class system::git {
    package { "git":
      ensure => installed,
      before => Class["ezpublish::install"]
    }
}