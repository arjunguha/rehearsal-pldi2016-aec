[![Build Status](https://magnum.travis-ci.com/plasma-umass/rehearsal.svg?token=qLSQpCbsY9CMXsHZVJDd)](https://magnum.travis-ci.com/plasma-umass/rehearsal)

# Rehearsal: A Configuration Verification Tool for Puppet

## Vagrantfile

We've provided a [Vagrantfile](https://www.vagrantup.com) that creates a
VirtualBox VM with everything needed to run Rehearsal and its benchmarks.
After installing Vagrant, from the root directory of this repository, run:

    vagrant up --provider virtualbox

## Building from source

### Prerequisites

1. Oracle JDK 8

2. [Microsoft Z3 Theorem Prover 4.4.1](https://github.com/Z3Prover/z3/releases/tag/z3-4.4.1)

   After installation, place the `z3` executable in your `PATH`.

3. [sbt](http://www.scala-sbt.org) version 0.13.9 or higher

4. [scala-smtlib](https://github.com/regb/scala-smtlib)

   This project is not published to Maven Central or any other repository.
   To install:

   ```
   git clone https://github.com/regb/scala-smtlib.git
   cd scala-smtlib
   git checkout 711e9a1ef994935482bc83ff3795a94f637f0a04
   sbt publish-local
   ```

### Building

From the root directory of the repository:

```
sbt compile
```

### Testing

```
sbt test
```
