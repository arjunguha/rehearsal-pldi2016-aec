$base_path = "<base path where you want to store your app, i.e. /var/webapps>"
$app_name = "<name of your webapp i.e. jabomly>"
$app_module_name = "<name of the Python module containing your Django WSGI module, i.e. jabomly>"
$domain = "<domain(without www) on which you want the service to run, i.e. jabomly.com (www redirect will occur by default)>"
$repo_url = "<git url of a repo containing your Django project/app, i.e. git@github.com:jodo/jabomly.git>"
$db_name = "<database name to use for your app>"
$db_username = "<database username to use for your app>"
$db_password = "<database password to use for your app>"

include machine
