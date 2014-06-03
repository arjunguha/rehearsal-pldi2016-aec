class { "devbox":
    hostname => "some-dev-box", # Make sure this maps to the address above
    documentroot => "web", # Apache documentroot eg: www, web, public_html etc
    gitUser => "Your full name",
    gitEmail => "Your email address"
}
