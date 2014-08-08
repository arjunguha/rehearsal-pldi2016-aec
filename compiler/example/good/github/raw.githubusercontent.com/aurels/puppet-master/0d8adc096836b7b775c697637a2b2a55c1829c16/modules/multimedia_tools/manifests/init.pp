class multimedia_tools {
  package { 'lame':           ensure => present }
  package { 'sox':            ensure => present }
  package { 'libsox-fmt-mp3': ensure => present }
  package { 'ffmpeg':         ensure => present }
  # id3 ?
}
