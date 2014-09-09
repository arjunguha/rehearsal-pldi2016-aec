class rails::params (
  # admin settings
  $admin_email = "admin@example.com",
  $admin_name = "Admin User",
  $admin_username = "admin",
  $admin_password = "changeme123",
  # database settings
  $database_type = "postgresql",
  $database_host = "localhost",
  $database_port = "5432",  
  $database_name = "rails",
  $database_username = "rails",
  $database_password = "changeme123.",
  # service settings
  $bind = "0.0.0.0",
  $port = "8080",
  # daemon settings
  $username = "ubuntu",
  $group = "ubuntu",
  $home = "/home/ubuntu",
  $repository_path = "/home/ubuntu/repo",
  $mode = "production") {
}