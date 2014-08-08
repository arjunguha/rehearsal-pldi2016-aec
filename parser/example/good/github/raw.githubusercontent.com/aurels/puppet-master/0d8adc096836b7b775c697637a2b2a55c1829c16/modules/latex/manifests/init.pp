class latex {
  package { 'pdftk':                     ensure => present }
  package { 'texlive-full':              ensure => present }
  package { 'texlive-xetex':             ensure => present }
  package { 'texlive-latex-recommended': ensure => present }
}
