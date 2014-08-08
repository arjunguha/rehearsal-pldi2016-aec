class params
{
  # Enable XDebug ( "0" | "1" )
  $use_xdebug = "0" 

  # Mysql
  $mysql_user = "root"
  $mysql_password = "root"
  $mysql_database = "database"
  $mysql_backup_dir = "/srv/config/backups/"

  # WWW Root
  $wwwroot = "/srv/www/"

  # Known hosts
  $ssh_known_hosts = []

  # Lemonstand installer
  $app_installer = "http://res.lemonstandapp.com/release/lemonstand_installer.zip"

  # Lemonstand license
  $license_holder = ""
  $license_serial = ""

  # Lemonstand urls
  $backend_url = "backend"
  $config_url = "config_tool"

  # Lemonstand user
  $user_firstname = "Master"
  $user_lastname = "Admin"
  $user_email = "admin@admin.com"
  $user_username = "admin"
  $user_password = "admin"

  # Lemonstand themes and data
  $use_default_theme = "1"
  $use_default_theme_twig = "1"
  $use_demo_data = "1"
  $encypt_key = "encryption"
}