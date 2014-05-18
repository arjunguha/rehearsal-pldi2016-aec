# Author: Kumina bv <support@kumina.nl>

# Class: kbp_vim
#
# Actions:
#   Undocumented
#
# Depends:
#   Undocumented
#   gen_puppet
#
class kbp_vim {
  gen_vim::global_setting {
    "syntax on":;
    "set ai":;
    "set ts=8":;
    "set bg=dark":;
    "set list":;
    "set listchars=tab:»˙,trail:•":;
    "set hlsearch":;
    "set ruler":;
    "autocmd FileType puppet set textwidth=140":
      ensure => "absent";
    "autocmd FileType puppet set tabstop=2":;
    "autocmd FileType puppet set expandtab":;
    "autocmd FileType puppet set shiftwidth=2":;
    'silent execute "!mkdir -p ~/.tmp"':;
    ["set backupdir=~/.tmp/","set directory=~/.tmp/"]:
      require => Gen_vim::Global_setting['silent execute "!mkdir -p ~/.tmp"'];
    "autocmd FileType python set tabstop=4":;
    "autocmd FileType python set shiftwidth=4":;
    "autocmd FileType python set expandtab":;
  }

  # This setting only works for vim in Squeeze (with backports) or higher
  if versioncmp($lsbmajdistrelease, 5) > 0 {
    gen_vim::global_setting {
      "autocmd FileType puppet set colorcolumn=167":;
      "autocmd FileType python set colorcolumn=81":;
    }
  }

  if $lsbdistcodename == 'squeeze' {
    gen_apt::preference { ['vim', 'vim-common', 'vim-runtime']:; }
  }
}

# Class: kbp_vim::puppet
#
# Actions:
#   Undocumented
#
# Depends:
#   Undocumented
#   gen_puppet
#
class kbp_vim::puppet {
  gen_vim::addon { "puppet":
    package => "vim-puppet";
  }
}
