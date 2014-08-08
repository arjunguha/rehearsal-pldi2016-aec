define gsettings(
  $schema,
  $key,
  $value,
  $level = '50'
) {
  include gsettings::setup
  realize Exec["glib-compile-schemas"]
  $override_path = "${gsettings::setup::schemas_path}/${level}_${schema}_${key}.gschema.override"

  file{"gsettings-default ${override_level}_${schema}_${key}":
    ensure  => "present",
    path    => "$override_path",
    owner   => "root",
    group   => "root",
    mode    => "0644",
    content => "[${schema}]\n  ${key}=${value}\n",
    notify  => Exec["glib-compile-schemas"],
  }
}
