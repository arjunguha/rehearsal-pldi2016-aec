---
layout: default
---

## Benchmarks

To generate the graphs in the paper (Figure 12), run the following commands
from the source code root (`~/rehearsal` on the virtual machine and
`/vagrant` using Vagrant):

    cd results && make

This will generate three PDF files in the `results` directory.

*NOTE*: For ease of evaluation, the script is modifed from what we used
for the paper:

- The script just runs 1 trial. This can be changed by editing
  `TRIALS` in `results/Makefile`.

- Each test has a 5 minute timeout. This can be changed by editing
  the `5.minutes` in `src/main/scala/Main.scala`.

- The IRC benchmark, which times out after ten minutes, is not run.
  To run it, remove `onlyPruning = true` from `scripts/Benchmarks.scala`.

## Command-line Tool

It is straightforward to add new benchmarks, but we've created a rough
command-line tool that checks determinism and idempotence (if determinism-checking
succeeds). From the source code root, run:

    ./rehearsal check --filename <FILENAME> --os <OS>

The supported values for *<OS>* are `ubuntu-trusty` and `centos-6`.

## Examples

- There are several small examples in the `examples` directory, all of
  which can be run with `--os ubuntu-trusty`. For example:

  ```
  $ ./rehearsal check --filename examples/carol-nondet.pp --os ubuntu-trusty
  Checking if manifest is deterministic ... FAILED.
  ```

  Error reporting is quite rudimentary, but the `rehearsal.log` file describes
  the scenario that triggers the bug.

- There are larger examples in `parser-tests/good`, including the benchmarks
  used in the paper. Some of these require `--os centos-6` instead of
  ``--os ubuntu-trusty`. The file `scripts/Benchmarks.scala` uses the right
  `--os` flag when analyzing these files.

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
    file{"/bin": ensure => directory }
    file{"/usr": ensure => directory }

    File {
      owner => "root"
    }
    File {
      group => "root"
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

