class ruby1_8 {

    case $operatingsystem {
        gentoo: {
          $ruby_package = "dev-lang/ruby"
          $ruby_version = "1.8.7_p357"
          $rubygems_package = "dev-ruby/rubygems"
        }
        default: {
          $ruby_package = "ruby1.8"
          $ruby_version = "installed"
          $rubygems_package = "rubygems1.8"
        }
    }

    package { "$ruby_package":
        ensure => "$ruby_version"
    }

    package { "$rubygems_package":
        ensure => "installed",
        require => Package["$ruby_package"]
    }
}

