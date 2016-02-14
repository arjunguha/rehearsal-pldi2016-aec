---
layout: default
---

We do not expect all readers to be familiar with the Puppet language.
The paper attempts to be self-contained and has several examples of Puppet,
but limits itself to a tiny fragment of Puppet. Rehearsal handles a much
larger subset of Puppet, which we illustrate below. We conclude with
examples of Puppet that Rehearsal cannot handle.


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
