---
layout: default
title: Arjun Guha
---


### Examples Rehearsal can handle

####Creating Resources

```puppet
file{ '/myfile': content => 'hello' }

file{ '/mydirectory': ensure => 'directory' }
file{ '/deletedfile': ensure => 'absent' } </br>
user{ 'myuser': name => 'Bob' }
ssh_authorized_key{ 'mykey': key => 'SMUBukLpUpCQgZ' }
```

<h4>Defining Dependencies</h4>

<p>
  The following four programs are equivalent.
  <ul>
  <li>Using explicit edges: </br>
    <code>
      file{ '/mydir': ensure => 'directory' } </br>
      file{ '/mydir/myfile': ensure => 'present' } </br>
      File{'/mydir'} -> File{'/mydir/myfile'}
    </code> </br>
    OR </br>
    <code>
      file{ '/mydir': ensure => 'directory' } </br>
      file{ '/mydir/myfile': ensure => 'present' } </br>
      File{'/mydir/myfile'} <- File{'/mydir'}
    </code>
  </li>
  <li>Using <code>before</code> attribute: </br>
    <code>
      file{ '/mydir': ensure => 'directory', before => File['mydir/myfile'] } </br>
      file{ '/mydir/myfile': ensure => 'present' }
    </code>
  </li>
  <li>Using <code>require</code> attribute: </br>
    <code>
      file{ '/mydir': ensure => 'directory' } </br>
      file{ '/mydir/myfile': ensure => 'present', require => File['mydir'] }
    </code>
  </li>
</p>

<h4>Defining new Resource Types (defined types)</h4>
<p>The folowing programs are equivalent.
  <ul>
  <li>Without parameters:</br>
    <code>
      define mytype { </br>
        <tab1>file{'/myfile': content => "hello" }</br></tab1>
      }</br>
      mytype{'myinstance': }
    </code>
  <li>With parameters</br>
    <code>
      define mytype($str) { </br>
        <tab1>file{'/myfile': content => $str }</br></tab1>
      }</br>
      mytype{'myinstance': str => "hello" }
    </code>
  </ul>
</p>