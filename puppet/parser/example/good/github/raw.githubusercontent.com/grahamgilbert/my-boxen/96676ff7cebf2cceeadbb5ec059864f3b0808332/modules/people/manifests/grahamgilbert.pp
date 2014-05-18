class people::grahamgilbert{
    include people::grahamgilbert::params
    
    class {'people::grahamgilbert::homebrew': } ->
    class {'people::grahamgilbert::applications': } ->
    class {'people::grahamgilbert::files': } ->
    class {'people::grahamgilbert::config': } ->
    class {'people::grahamgilbert::dock': } ->
    class {'people::grahamgilbert::gems': } ->
    class {'people::grahamgilbert::loginitems': } ->
    class {'people::grahamgilbert::ssh_keys': } ->
    class {'projects::all': }
    
}
