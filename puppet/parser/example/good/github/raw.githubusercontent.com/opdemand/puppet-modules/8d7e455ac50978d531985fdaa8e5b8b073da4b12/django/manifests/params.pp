class django::params (
  # admin settings
  $admin_email = "admin@example.com",
  $admin_name = "Admin User",
  $admin_username = "admin",
  $admin_password = "changeme123",
  # database settings
  $database_type = "postgresql",
  # service settings
  $bind = "0.0.0.0",
  $port = "8080",
  # daemon settings
  $username = "ubuntu",
  $group = "ubuntu",  
  $home = "/home/ubuntu",
  $repository_path = "/home/ubuntu/repo") {
}