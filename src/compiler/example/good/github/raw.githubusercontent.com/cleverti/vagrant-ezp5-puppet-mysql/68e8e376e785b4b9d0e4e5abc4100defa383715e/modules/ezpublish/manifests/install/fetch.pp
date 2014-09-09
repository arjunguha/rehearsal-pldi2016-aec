define ezpublish::install::fetch ($www, $ezpublish_src, $ezpublish_folder, $ezpublish, $type) {
  case $type {
    "tar": {
      ezpublish::install::fetch::tar{ "tar" : 
        www => $www, 
        ezpublish_src => $ezpublish_src, 
        ezpublish_folder => $ezpublish_folder, 
        ezpublish => $ezpublish
      }
    }
    "local": {
      ezpublish::install::fetch::local{ "local" : 
        www => $www, 
        ezpublish_src => $ezpublish_src, 
        ezpublish_folder => $ezpublish_folder, 
        ezpublish => $ezpublish
      }
    }
    "zip": {
      ezpublish::install::fetch::zip{ "zip" :
        www => $www, 
        ezpublish_src => $ezpublish_src, 
        ezpublish_folder => $ezpublish_folder, 
        ezpublish => $ezpublish
      }
    }
    "git": {
      ezpublish::install::fetch::git{ "git" :
        www => $www, 
        ezpublish_folder => $ezpublish_folder, 
      }
    }
  }
}