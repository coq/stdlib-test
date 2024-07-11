{
    if ($1 != substr($3, 1, length($3)-1)) {
        print $0
    }
}
