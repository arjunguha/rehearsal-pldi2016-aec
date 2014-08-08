class gitorious::repo {
	if $::operatingsystem == 'Centos' {
		if $::operatingsystemrelease != '6.0' {
			realize(Yumrepo['centosplus'])
		}
		realize(Yumrepo['inuits', 'inuits-gems', 'rpmforge'], File['rpmforge-gpg-key'])
	}
}
