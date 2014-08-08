# Class: vim
#
# This module manages vim and is included by the generic module and
# applied to all nodes
#
# Sample Usage: include vim
#
class vim {

    package { "vim-enhanced": }

    file { "/etc/vimrc":
        source  => "puppet:///modules/vim/vimrc-$operatingsystem",
        require => Package["vim-enhanced"],
        links   => follow,
    } # file
} # class vim
