define foo::bar(){
	file{"/home/rian/hello": ensure => "absent"}
}


foo::bar { "/home": }