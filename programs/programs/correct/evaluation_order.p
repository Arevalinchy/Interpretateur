int f_id(int x) ::= {
    print "f\n";
    return x;
}

int g_id(int x) ::= {
    print "g\n";
    return x;
}

int sum(int x,int y) ::= {
    print "sum\n";
    return x+y;
}

null main() ::= {
    int x;
    x := sum(f_id(4),g_id(5));
    print x;
    print "\n";
}