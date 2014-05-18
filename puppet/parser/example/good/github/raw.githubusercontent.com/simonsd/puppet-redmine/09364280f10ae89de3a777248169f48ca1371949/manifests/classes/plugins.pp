class redmine::plugins {
	@redmine::plugin {
		'gitolite':
			name => 'redmine_git_hosting',
			url => 'git+ssh://git@git.dev.inuits.be:2222/redmine-plugins/redmine_git_hosting.git',
			gems => ['lockfile', 'inifile', 'net-ssh'],
			require => Class['gitolite'];

		'gitosis':
			name => 'redmine_gitosis',
			url => 'https://github.com/y8/redmine-gitosis.git',
			gems => ['lockfile', 'inifile', 'net-ssh'];

		'gravatar-helper':
			name => 'gravatar-helper',
			url => 'http://mattmccray.com/svn/rails/plugins/gravatar_helper';

		'bulk time entry':
			name => 'bulk time entry',
			url => 'https://github.com/edavis10/redmine-bulk_time_entry_plugin.git';

		'pastebin':
			name => 'redmine_pastebin',
			url => 'git+ssh://git@git.dev.inuits.be:2222/redmine-plugins/redmine_pastebin.git';

		'dmsf':
			name => 'dmsf',
			url => 'http://redmine-dmsf.googlecode.com/svn/';

		'docpu':
			name => 'redmine_doc_pu',
			url => 'https://github.com/erikkallen/redmine_doc_pu.git',
			deps => ['texlive', 'texlive-latex'],
			gems => ['RedCloth'];

		'http_auth':
			name => 'redmine_http_auth',
			url => 'git+ssh://git@git.dev.inuits.be:2222/redmine-plugins/redmine_http_auth.git';

		'kanban':
			name => 'redmine_kanban',
			url => 'git+ssh://git@git.dev.inuits.be:2222/redmine-plugins/redmine_kanban.git',
			gems => ['aasm', 'block_helpers'];

		'timesheet':
			name => 'timesheet_plugin',
			url => 'git+ssh://git@git.dev.inuits.be:2222/redmine-plugins/timesheet_plugin.git';

		'webdav':
			name => 'redmine_webdav',
			url => 'git+ssh://git@git.dev.inuits.be:2222/redmine-plugins/redmine_webdav.git',
			require => Redmine::Plugin['http_auth'],
			gems => ['unicode', 'shared-mime-info'];

		'schedules':
			name => 'redmine_schedules',
			url => 'git+ssh://git@git.dev.inuits.be:2222/redmine-plugins/redmine_schedules.git',
			gems => ['holidays'];

		'knowledgebase':
			name => 'knowledgebase',
			url => 'https://github.com/alexbevi/redmine_knowledgebase.git',
			gems => ['acts_as_viewed', 'acts_as_rated', 'acts_as_taggable_on_steroids'];

		'stuff_to_do':
			name => 'stuff_to_do',
			url => 'https://github.com/edavis10/redmine-stuff-to-do-plugin.git';

		'redcmd':
			name => 'redcmd',
			url => 'https://github.com/textgoeshere/redcmd.git';

		'theme_changer':
			name => 'theme_changer',
			url => 'https://bitbucket.org/haru_iida/redmine_theme_changer';

		'sidebar_content':
			name => 'sidebar_plugin',
			url => 'http://svn.s-andy.com/redmine-sidebar';

		'tags':
			name => 'redmine_tags',
			url => 'https://github.com/ixti/redmine_tags.git',
			gems => ['acts-as-taggable-on'];

		'hudson':
			name => 'redmine_hudson',
			url => 'https://github.com/AlekSi/redmine_hudson.git';

		'issue_relations':
			name => 'redmine_context_menu_relations',
			url => 'https://github.com/edavis10/redmine_context_menu_relations.git';

		'irc_gateway':
			name => 'redmine_irc_gateway',
			url => 'https://github.com/hackers/redmine_irc_gateway.git';

		'checkout':
			name => 'redmine_checkout',
			url => 'http://dev.holgerjust.de/projects/redmine-checkout/repository';

		'markdown_formatter':
			name => 'redmine_markdown_formatter',
			url => 'https://github.com/bitherder/redmine_markdown_formatter.git',
			gems => 'rdiscount';

		'scmacros':
			name => 'redmine_scmacros',
			url => 'https://github.com/gpr/redmine_scmacros.git';

		'graphviz':
			name => 'wiki_graphviz_plugin',
			url => 'https://github.com/tckz/redmine-wiki_graphviz_plugin.git';

		'groupwatch':
			name => 'redmine_watchers_by_group',
			url => 'https://github.com/alvila/redmine_watchers_by_group.git';

		'sprints':
			name => 'redmine_sprints',
			url => 'git+ssh://git@git.dev.inuits.be:2222/redmine-plugins/redmine_sprints.git',
			gems => ['googlecharts', 'mini_magick'],
			require => Redmine::Plugin['attachment_fu'];

		'attachment_fu':
			name => 'attachment_fu',
			url => 'git+ssh://git@git.dev.inuits.be:2222/redmine-plugins/attachment_fu.git';
	}

	if $redmine::plugins != [] {
		realize(Redmine::Plugin[$redmine::plugins])

		exec {
			'db:migrate_plugins':
				command => 'rake db:migrate_plugins',
				cwd => "$redmine::home",
				path => "$ruby::bin_dir",
				environment => 'RAILS_ENV=production',
				require => Redmine::Plugin[$redmine::plugins];
		}
	}
}
