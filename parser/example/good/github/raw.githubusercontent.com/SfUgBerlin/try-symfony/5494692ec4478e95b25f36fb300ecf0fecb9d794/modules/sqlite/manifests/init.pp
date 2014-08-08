class sqlite {
    case $operatingsystem {
        Debian,Ubuntu:  { include sqlite::debian}
        default: { fail "Unsupported operatingsystem ${operatingsystem}" }
    }
}