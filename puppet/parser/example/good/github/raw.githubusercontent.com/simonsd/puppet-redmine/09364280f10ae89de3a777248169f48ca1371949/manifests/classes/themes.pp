class redmine::themes {
	@redmine::theme {
		'pepper':
			url => 'https://github.com/koppen/redmine-pepper-theme.git';

		'aurora':
			url => 'https://github.com/jorgebg/redmine-aurora-theme.git';

		'innerboard':
			url => 'https://github.com/huacnlee/redmine-theme-innerboard.git';

		'pixelcookers':
			url => 'https://github.com/pixel-cookers/RedmineThemePixelCookers.git';

		'squeejee':
			url => 'https://github.com/edavis10/squeejee_theme.git';

		'martini':
			url => 'https://github.com/bevanr/martini.git';
	}

	if $redmine::themes {
		realize(Redmine::Theme[$redmine::themes])
	}
}
