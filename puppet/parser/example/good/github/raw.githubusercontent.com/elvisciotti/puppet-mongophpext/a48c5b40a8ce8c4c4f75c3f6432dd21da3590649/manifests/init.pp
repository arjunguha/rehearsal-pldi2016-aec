# install mongo db pecl extension
class mongophpext {
    package { "make": 
        ensure => "installed"
    }

    exec { "pecl install mongo":
        command => "pecl install mongo",
        path => "/usr/bin/",
        require => Package["make"],
        unless => 'pecl info mongo'
    }
    
    file { "/etc/php5/conf.d/mongo.ini":
        content=> 'extension=mongo.so',
        require => Exec["pecl install mongo"]
    }
    
}