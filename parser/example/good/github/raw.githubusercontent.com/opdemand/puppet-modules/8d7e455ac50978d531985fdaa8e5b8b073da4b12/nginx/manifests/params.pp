class nginx::params (
  $num_listeners = 1,
  $public_root = "/home/ubuntu/repo/public",
  $template_name = "default",
  $access_port = 80,
  $start_port = 5000,
  $server_name = $ec2_public_hostname,
  # required fields
  $app_name) {
}