class people::grahamgilbert::config (
	$my_homedir   = $::people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $::people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $::people::grahamgilbert::params::my_username
	){	

        include osx::global::expand_save_dialog
        include osx::universal_access::ctrl_mod_zoom
        include osx::finder::unhide_library
		
		osx_chsh { $::luser:
			shell   => '/opt/boxen/homebrew/bin/zsh',
			require => Package['zsh'],
		}
		
		file_line { 'add zsh to /etc/shells':
			path    => '/etc/shells',
			line    => "${boxen::config::homebrewdir}/bin/zsh",
			require => Package['zsh'],
		}
		
		if !defined(File["${my_sourcedir}/Mine"]){
			file {"${my_sourcedir}/Mine":
				ensure => directory,
			}
		}
        
        # Stop Preview re-opening documents
		boxen::osx_defaults { 'Stop Preview re-opening documents':
			  ensure => present,
			  domain => 'com.apple.Preview',
			  key    => 'NSQuitAlwaysKeepsWindows',
			  value  => 'NO',
		}
        
        boxen::osx_defaults { 'Enable AirDrop on all interfaces':
            ensure => present,
            domain => 'com.apple.NetworkBrowser',
            key    => 'BrowseAllInterfaces',
            value  => 'true',
            type   => 'bool',
            user   => $::boxen_user
        }
        
        boxen::osx_defaults { 'Copy text from QuickLook':
            ensure => present,
            domain => 'com.apple.finder',
            key    => 'QLEnableTextSelection',
            value  => 'YES',
        }
            
        # Config the luggage
		file { "/usr/local/share/luggage/luggage.local":
            ensure  => link,
            target  => "${my_sourcedir}/Mine/luggage_local/luggage.local",
            require => Boxen::Project['luggage_local']
        }
        
        
        # CocoaPython Template for Xcode
		repository { 'Xcode4CocoaPythonTemplates':
			source => 'gregneagle/Xcode4CocoaPythonTemplates',
			path   => "${my_sourcedir}/Others/Xcode4CocoaPythonTemplates",
			require => File["${my_sourcedir}/Others"],
		}
        
		file { "/Users/${::luser}/Library/Developer/Xcode/Templates":
			ensure  => link,
			target  => "${my_sourcedir}/Others/Xcode4CocoaPythonTemplates",
			require => Repository['Xcode4CocoaPythonTemplates']
		} 
		
		# TextMate
		
		repository { 'puppet-textmate-bundle':
			source  => 'puppet-textmate-bundle/puppet-textmate-bundle',
			path    => "${my_sourcedir}/Others/puppet-textmate-bundle",
			require => File["${my_sourcedir}/Others"],
		}
		
		/* file {"/Users/${::luser}/Library/Application Support/TextMate":
			ensure => directory,
		}
		
		file {"/Users/${::luser}/Library/Application Support/TextMate/Managed":
			ensure => directory,
		}
		
		file {"/Users/${::luser}/Library/Application Support/TextMate/Managed/Bundles":
			ensure => directory,
		} */
		
		file { "/Users/${::luser}/Library/Application Support/TextMate/Managed/Bundles/Puppet.tmbundle":
			ensure  => link,
            force   => true,
			target  => "${my_sourcedir}/Others/puppet-textmate-bundle",
			require => Repository['puppet-textmate-bundle']
		} 
        
		boxen::osx_defaults { 'TextMate File Browser Placement':
			  ensure => present,
			  domain => 'com.macromates.TextMate.preview',
			  key    => 'fileBrowserPlacement',
			  value  => 'left',
		}
        # Chocolat
		
		repository { 'Chocolat Truffles':
			source => 'grahamgilbert/chocolat-truffles',
			path   => "${my_sourcedir}/Mine/chocolat-truffles",
			require => [
			             File["${my_sourcedir}/Mine"],
			             File["/Users/${::luser}/Library/Application Support/Chocolat"],
			             ]
		}
		
		file {"/Users/${::luser}/Library/Application Support/Chocolat":
			ensure => directory,
		}
		
		file { "/Users/${::luser}/Library/Application Support/Chocolat/Truffles":
			ensure  => link,
			target  => "${my_sourcedir}/Mine/chocolat-truffles",
			require => Repository['Chocolat Truffles']
		}
		
		repository { 'oh-my-zsh':
			source => 'grahamgilbert/oh-my-zsh',
			path   => "/Users/${::luser}/.oh-my-zsh",
            #ensure => latest,
		 }
		
		file { "/Users/${::luser}/.zshrc":
			ensure  => link,
			target  => "/Users/${::luser}/.oh-my-zsh/grahams-zshrc",
			require => Repository['oh-my-zsh']
		}
		

		git::config::global { 'user.email':
			value  => 'graham@grahamgilbert.com'
		}
		
		Boxen::Osx_defaults {
		  user => $::luser,
		}
		
		boxen::osx_defaults { 'Chocolat Theme':
			  ensure => present,
			  domain => 'com.chocolatapp.Chocolat',
			  key    => 'CHActiveTheme',
			  value  => 'Owl',
		}
		
		boxen::osx_defaults { 'Chocolat Font Size':
			  ensure => present,
			  domain => 'com.chocolatapp.Chocolat',
			  key    => 'CHDefaultFontSize',
			  value  => 15,
		 }
		 
		 boxen::osx_defaults { 'Finder Status Bar':
			 ensure	=> 	present,
			 domain	=>	'com.apple.finder',
			 key	=>	'ShowStatusBar',
			 value	=>	'YES',
		}
		
		boxen::osx_defaults { 'Disable the "Are you sure you want to open this application?" dialog':
			key    => 'LSQuarantine',
		  	domain => 'com.apple.LaunchServices',
		  	value  => 'true',
		}
		
		boxen::osx_defaults { 'Remove Alfred Hat from the Menu Bar':
			domain	=> 'com.alfredapp.Alfred',
			key		=> 'appearance.hideStatusBarIcon',
			#type	=> 'BOOL',
			value	=> 'YES',
		}
            
        boxen::osx_defaults {
            'Prevent Time Machine from prompting to use new hard drives as backup volume':
              ensure => present,
              key    => 'DoNotOfferNewDisksForBackup',
              domain => 'com.apple.TimeMachine',
              value  => 'true',
              type   => 'bool',
              user   => $::boxen_user,
        }
		
		boxen::osx_defaults { 'Make Go2Shell Use iTerm':
			domain	=> 'com.alice.mac.go2shell',
			key		=> 'usingTerminal',
			#type	=> 'BOOL',
			value	=> '2',
		}
		
		boxen::osx_defaults { 'Show time connected in the VPN menubar item':
            domain => 'com.apple.networkConnect',
            key    => 'VPNShowTime',
            type   => 'bool',
            value  => 'true',
        }
		
		#boxen::osx_defaults { 'Stop iTerm nagging about quitting':
		#	domain	=> 'com.googlecode.iterm2',
		#	key		=> 'PromptOnQuit',
			#type	=> 'BOOL',
		#	value	=> 'NO',
		#}

		boxen::osx_defaults { 'Disk util debug menu':
			domain	=> 'com.apple.DiskUtility',
			key		=> 'DUDebugMenuEnabled',
			value	=> 1,
		}
		
		boxen::osx_defaults {'Four finger trackpad swipe':
			domain => 'com.apple.driver.AppleBluetoothMultitouch.trackpad',
			key    => 'TrackpadFourFingerVertSwipeGesture',
			value  => 2,
		}
		
		##hide away from meraki
		if !defined(File['/etc/meraki']){
			file { '/etc/meraki':
				ensure	=>	directory,
			}
		}
		
		file {'/etc/meraki/ci.conf':
			ensure	=> present,
			source	=> 'puppet:///modules/people/grahamgilbert/ci.conf',
            owner   => 0,
            group   => 0,
            mode    => '0644',
		}
        
		file {'/etc/sysctl.conf':
			ensure	=> present,
			source	=> 'puppet:///modules/people/grahamgilbert/sysctl.conf',
            owner   => 0,
            group   => 0,
            mode    => '0644',
		}
        
        # Install the ksdiff tool
        
        file {'/usr/local':
            ensure => 'directory',
            owner  => 0,
            group  => 0,
        }
        
        file {'/usr/local/bin':
            ensure => 'directory',
            owner  => 0,
            group  => 0,
        }
        
        file {'/usr/local/bin/ksdiff':
            owner   => 0,
            group   => 0,
            mode    => '0755',
            source  => '/Applications/Kaleidoscope.app/Contents/Resources/bin/ksdiff',
            require => [File['/usr/local/bin'],Package['Kaleidoscope']],
        }
}
