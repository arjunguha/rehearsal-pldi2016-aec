# TODO: after turning this into a module add the rubyee shit to a site-unicorn module.
class unicorn {
  package {
    "unicorn":
      ensure   => 'installed',
      provider => 'gem';
  }
}
