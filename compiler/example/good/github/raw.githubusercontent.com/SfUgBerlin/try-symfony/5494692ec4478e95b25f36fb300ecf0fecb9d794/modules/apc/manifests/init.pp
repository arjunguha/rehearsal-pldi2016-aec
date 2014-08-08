class apc {
    case $operatingsystem {
        Debian,Ubuntu:  { include apc::debian}
        default: { fail "Unsupported operatingsystem ${operatingsystem}" }
    } 
}