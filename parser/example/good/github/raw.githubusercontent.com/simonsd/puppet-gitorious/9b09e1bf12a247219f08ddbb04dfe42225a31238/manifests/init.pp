import 'classes/*'

class gitorious (
	$dbuser    = 'gitorious',
	$dbpass    = 'gitorious',
	$webserver = 'apache2',
	$home      = '/usr/share/gitorious',
	$host
) {
  class {
    'repos':;
    'activemq':;
    'apache':
      devel => yes;
    'passenger':;
    'mysql':
      rootpass => 'foobar';
  }

  class{'gitorious::pre':} ->
  class{'gitorious::repo':} ->
  class{'gitorious::depends':} ->
  class{'gitorious::user':} ->
  class{'gitorious::core':} ->
  class{'gitorious::dbconf':} ->
  class{'gitorious::config':} ->
  class{'gitorious::services':}

  Exec { path => '/usr/local/bin:/usr/local/sbin:/usr/bin:/usr/sbin:/bin:/sbin' }
}
