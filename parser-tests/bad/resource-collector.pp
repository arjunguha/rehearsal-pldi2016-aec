define foo::bar(){
	file{"/home/rian/hello": ensure => "absent"}
}

File<| owner == 'carol' |> { mode => "go-rwx" }
foo::bar { "/home": }