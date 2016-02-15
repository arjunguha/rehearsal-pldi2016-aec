---
layout: default
---

This website is for members of the PLDI 2016 Artifact Evaluation Committee.

# Puppet Crash-Course

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

- Using the *require* attribute:

  ```puppet
    file{ '/mydir': ensure => 'directory' }
    file{ '/mydir/myfile': ensure => 'present', require => File['mydir'] }
  ```

## Arrays
  
- Basic syntax:
  
  ```puppet
    $x = [ "a", "b", ]
  ```

- Arrays can be used to define multiple dependency relations. For example:

  ```puppet
    [File['dir'], Package['pkg']] -> [File['file1'], File['file2']]
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

## Updating Resources

A user can change the attributes for all resources of a certain type:

  ```puppet
    file{"/bin": ensure => present }
    file{"/usr": ensure => present }

    File {
      content => "hello"
    }
  ```

## Classes

- Include-like behavior using ```puppet include ```:

  ```puppet
    class myclass {
      notify{"baz": message => "/a"}
    }
    include myclass
  ```

- Include-like behavior using ```puppet require ```:

  ```puppet
    class myclass {
      notify{"baz": message => "/a"}
    }
    require myclass
  ```

- Resource-like behavior (without parameters):

  ```puppet
    class myclass {
      notify{"baz": message => "/a"}
    }
    class{"myclass": }
  ```

- Resource-like behavior (with parameters):

  ```puppet
    class myclass($x) {
      notify{"baz": message => $x}
    }
    class{"myclass":
      x => "/a"
    }
  ```
## Conditionals

- If as an expression assigned to a variable:

  ```puppet $x = if (true) { 1 } else { 2 } ```

- If as a statement:

  ```puppet
      if "localhost.localdomain" != $::fqdn {
        include postfix
      }
  ```

- Else-if:

  ```puppet
      $y = if($a == 1) {
        "one"
      } else if ($a == 2) {
        "two"
      }
  ```

- Ternary Expressions

  ```puppet
    $a = true
    $b = 900

    $x = $a ? $b : $b ? $y : $z
  ```

## Case statements

- Without defalut:

  ```puppet
      case "foo" {
        "bar": { file{"/foo": } }
        "baz": { file{"/foo": } }
      }
  ```

- With default:

  ```puppet
      case "foo" {
        "bar": { file{"/fooz": } }
        default: { file{"/fooz": } }
      }
  ```

## Stages

- Stages can be used to group resources and/or classes and create dependencies between them.
  *main* is the default stage.

  ```puppet
    stage { 'files': before => Stage['packages'] }
    stage { 'packages': before => Stage['main'] }

    file { 'myfile': stage => 'files' }
    package { 'mypackage': stage => 'packages' }
}
  ```

## What Rehearsal Cannot handle:

- Resource types other than: file, package, service, user, notify, and ssh-authorized-key

- Shell scripts: 

  ```puppet
    exec { 'refresh_cache':
      command => 'refresh_cache 8600',
      path    => '/usr/local/bin/:/bin/',
    }
  ```
