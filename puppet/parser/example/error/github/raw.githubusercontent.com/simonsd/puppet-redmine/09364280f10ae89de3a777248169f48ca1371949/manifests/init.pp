import 'classes/*'
import 'definitions/*'

class redmine (
	$servername,
	$serveralias = [],
	$production_db = 'redmine_production',
	$devel_db = 'redmine_devel',
	$dbuser = 'redmine',
	$dbpass = 'redmine',
	$dbhost = 'localhost',
	$dbserver = 'localhost',
	$home = '/usr/share/redmine',
	$plugins = [],
	$mail_user = 'redmine',
	$mail_pass = 'redmine',
	$mail_auth = 'plain',
	$mail_domain = 'redmine.org',
	$mail_port = '587',
	$mail_smtp = 'smtp.redmine.org',
	$mail_tls = 'true',
	$themes = []
) {
	if ! defined(Class['::repos']) { include ::repos }

	class {
		'redmine::pre':
			before => Class['redmine::depends'];
		'redmine::depends':
			before => Class['redmine::config'];
		'redmine::config':
			before => Class['redmine::dbconf'];
		'redmine::dbconf':
			require => Service['mysqld'],
			before => Class['redmine::plugins'];
		'redmine::plugins':
			before => Class['redmine::themes'];
		'redmine::themes':;
	}

    Exec {
		path=>'/bin:/sbin:/usr/bin:/usr/sbin:/usr/local/bin'
	}
}
