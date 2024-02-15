int f1(int x, int y) ::= {
    {
        x := x*x;
        y := y-1;
    }
    return (x+y);
}

int f2(var int x, int y) ::= {
    {
        x := x*x;
        y := y-1;
    }
    return (x+y);
}

int f3(int x,var int y) ::= {
    {
        x := x*x;
        y := y-1;
    }
    return (x+y);
}

int f4(var int x,var int y) ::= {
    {
        x := x*x;
        y := y-1;
    }
    return (x+y);
}

null main() ::= {
    int a;
    int b;
    int r;
    int t[1];
    t[0] := 2;
    a := 4;
    b := 3;
    r := f1(a,b);
    print "f1:\na: ";
    print a;
    print "\nb: ";
    print b;
    print "\nr: ";
    print r;
    a := 4;
    b := 3;
    r := f2(a,b);
    print "\n\nf2:\na: ";
    print a;
    print "\nb: ";
    print b;
    print "\nr: ";
    print r;
    a := 4;
    b := 3;
    r := f3(a,b);
    print "\n\nf3:\na: ";
    print a;
    print "\nb: ";
    print b;
    print "\nr: ";
    print r;
    a := 4;
    b := 3;
    r := f4(a,b);
    print "\n\nf4:\na: ";
    print a;
    print "\nb: ";
    print b;
    print "\nr: ";
    print r;

    a := 4;
    r := f1(a+4,t[0]);
    print "\n\nf1(a+4,t[0]):\nr: ";
    print r;

    a := 4;
    r := f4(a,a);
    print "\n\nf4 aliasé:\na: ";
    print a;
    print "\nr: ";
    print r;
    print "\n";
}