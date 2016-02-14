---
layout: default
---

# Accepted Version of the Paper

The accepted version of the paper is [available here (PDF)](rehearsal-accepted-version.pdf).

# Examples Rehearsal can handle

## Creating Resources

```puppet
file{ '/myfile': content => 'hello' }

file{ '/mydirectory': ensure => 'directory' }

file{ '/deletedfile': ensure => 'absent' }

user{ 'myuser': name => 'Bob' }

ssh_authorized_key{ 'mykey': key => 'SMUBukLpUpCQgZ' }
```

##  Defining Dependencies

The following four programs are equivalent.

-  Using explicit edges:

   ```puppet
    file{ '/mydir': ensure => 'directory' }
    file{ '/mydir/myfile': ensure => 'present' }
    File{'/mydir'} -> File{'/mydir/myfile'}
   ```

- Using explicit edges (alternative):

  ```puppet
  file{ '/mydir': ensure => 'directory' }
  file{ '/mydir/myfile': ensure => 'present' }
  File{'/mydir/myfile'} <- File{'/mydir'}
  ```

- Using the *before* attribute:

  ```puppet
    file{ '/mydir': ensure => 'directory', before => File['mydir/myfile'] }
    file{ '/mydir/myfile': ensure => 'present' }
  ```

- Using the *after* attribute:

  ```puppet
    file{ '/mydir': ensure => 'directory' }
    file{ '/mydir/myfile': ensure => 'present', require => File['mydir'] }
  ```

## Defining new Resource Types (defined types)

The folowing programs are equivalent.

- Without parameters:

  ```puppet
    define mytype {
      file{'/myfile': content => "hello" }
    }
    mytype{'myinstance': }
  ```

- With parameters:

  ```puppet
    define mytype($str) {
      file{'/myfile': content => $str }
    }
    mytype{'myinstance': str => "hello" }
  ```
