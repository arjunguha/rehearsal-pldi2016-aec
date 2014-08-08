/*
== Definition: selinux::fcontext

Changes the selinux context of files and directories.

Parameters:

- *$name*: file/dir name or regex
- *$ensure*: present/absent
- *$recursive*: apply to all subdirectories
- *$setype*: security context name

Example usage:

  # allow apache to read from here
  selinux::fcontext { "/var/www":
    ensure    => present,
    recursive => true,
    setype    => "httpd_sys_content_t"
  }

*/
define selinux::fcontext(
  $ensure = "present",
  $recursive = true,
  $setype
) {

  $path = $name

  $re = "^${path}\\s+.*\\s+\\w+:\\w+:${setype}:s0"

  if $recursive {
    $path_glob = "(/.*)?"
  } else {
    $path_glob = ""
  }

  if $ensure == "present" {
    $semanage = "--add"
    $grep     = "egrep -q"
  } else {
      $semanage = "--delete"
      $grep     = "! egrep -q"
  }

  exec { "semanage fcontext ${setype} ${path}${path_glob}":
    path    => "/usr/bin:/usr/sbin:/bin:/sbin",
    command => "semanage fcontext -a -t ${setype} \"${path}${path_glob}\"",
    unless  => "semanage fcontext --list | ( ${grep} '${re} )"
  }

  exec { "restorecon -R ${path}":
    path    => "/usr/bin:/usr/sbin:/bin:/sbin",
    command => "restorecon -R ${path}"
  }

}
