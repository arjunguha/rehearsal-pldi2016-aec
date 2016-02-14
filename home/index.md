---
layout: default
---

This website is for members of the PLDI 2016 Artifact Evaluation Committee.

# The Paper

The accepted version of the paper is [available here (PDF)](rehearsal-accepted-version.pdf).

## Author Response

The PLDI reviewers asked several questions that we clarified in the author
response. We've included portions of our author response that we believe
will help the AEC understand our paper.

### Does determinism actually matter?

Some reviewers wanted evidence that the Puppet community cares about
determinism. There are several articles and blog posts on the Web
that discuss Puppet and determinism, though some are quite confused. Here
is a sample:

1. [https://puppetlabs.com/blog/inside-puppet-about-determinism]

   This official blog post asserts that determinism is desirable, but stops
   short of saying "all Puppet manifests are deterministic" (since they are
   not).

2. [https://bugzilla.mozilla.org/show_bug.cgi?id=691654]

  This is an Mozilla infrastructure bug that reports a non-determinism error.

3. [http://kartar.net/2010/01/puppet-chef-deterministic-ordering-and-the-much-maligned-dsl/]

   This personal blog post by a Puppet employee asserts that Puppet is
   deterministic when the user correctly specifies all dependencies.
   Of course, correctly specifying all dependencies is the hard part!

There are scores of other posts, Bugzilla issues, and GitHub commits that
discuss determinism. ,They can be found by Googling "Puppet determinism".

### Does Idempotence actually matter?

The official Puppet documentation asserts that Puppet is idempotent:

  [https://docs.puppetlabs.com/guides/introduction.html#idempotency]

However, the examples in our paper show that this is not true. Individual
resources may be idempotent, but it is easy to create compound manifests
that are not idempotent.

### Limitations of the model (specifically, the model of packages)

Several reviewers wanted the paper to clarify the limitations of the model.
It was clear to Reviewer A that we don't model several
subtleties of packages, such as post-install scripts, and we will make this
clear earlier. We are considering alternative approaches: (1) analyzing
shell scripts to determine their effects and (2) actually installing
packages in a Docker container to better model their effects. We
believe it would be easy to plug in better package-models.

### Soundness and completeness

Our determinism-checking algorithm is sound and complete with respect to the
model of resources. However, the model makes simplifying assumptions (e.g., see
above), so the algorithm is not complete w.r.t. Puppet itself. We will make this
distinction clear.

### More details

A reviewer asked:

>  I think Figure 2 needs "/home/" added to the File resource in the dependency
>  declaration.

Since it is left out, the manifest simply assumes that /home is a directory in
all initial states. If /home were added, it would create the /home directory.
Both are valid, but it typically safe to assume that /home exists on Linux
systems.

A reviewer said:

>  You might want to explain here if you expect users to
>  choose one base system to check determinism against, or whether you check for
>  multiple OS versions simultaneously.

We will make it clear that the user has to choose a particular OS and version.
We've built support for Ubuntu 14.04 and CentOS 6. Our implementation
makes it easy to add support for more.

A reviewer was concerned that Section 2.2 discusses bugs that are not
non-determinism bugs:

- *Silent failure*: This is a kind of non-determinism bug that our tools catch.

- *Non-idempotence*: This is addressed in Section 5, and critically depends
  on checking non-determinism. We apologize that Section 5 is so terse. We
  would expand it in a revision.

- *Overconstrained dependencies*: We don't provide an automated tool to detect
  unnecessary dependencies, but it should be easy to build using
  the infrastructure that we have. Naturally, if the user manually removes
  dependencies, our determinism checker validates that they were safe to remove.

A reviewer said:

> The paper should be more clear about exactly what properties it considers to
> be sufficient and necessary for correctness.

Determinism is *necessary* for correctness, but it isn't *sufficient*. We will
make it clear that the paper doesn't address *sufficiency*. A full verification
would require the user to specify the intended behavior of the system. The
"Invariants" in Section 5 is a step in this direction.

>  - The introduction, "To the best of our knowledge, this is the first
>    paper to develop programming language techniques for Puppet or any
>    other system configuration language of its kind". What about
>    citations 5,9,and 10, from POPL, PLDI, and the Journal of Functional
>    Programming?

We apologize for the confusion. We meant that our submission is the first
that develops a semantics for languages such as Puppet, Chef, Ansible, etc.,
which are quite different from [5,9,10]. We will carefully scope our claim.

>  - why are SSH keys treated differently from other files?

>  - is it possible for Rehearsal to express an invariant that a package only
>    append to a file?

Since SSH authorized-keys are all appended to a single file and their order in
the file is irrelevant, we cannot model them precisely. Therefore, the paper
describes how we approximate SSH keys as a collection of files. We use a similar
trick to model CRON jobs. We are exploring using lenses to model more
sophisticated updates to files.

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
  
## Ternary Expressions

  ```puppet
    $a = true
    $b = 900

    $x = $a ? $b : $b ? $y : $z
  ```