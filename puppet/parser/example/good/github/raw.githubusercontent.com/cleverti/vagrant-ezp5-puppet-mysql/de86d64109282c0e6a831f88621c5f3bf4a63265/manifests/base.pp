if $env == "dev" {
    include system::git
    include httpd::xdebug
}
include system::ntpd
include system::motd
include system::firewall
include system::ssh
include system::imagick
include system::composer
include system::hosts
include httpd
include httpd::apc
include httpd::virtualhosts
include mysql
include mysql::createdb
include startup
include ezpublish
include ezpublish::ezfind
include ezpublish::install