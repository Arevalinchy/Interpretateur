null f(var int x) ::= x := x+1;

null main() ::= {
    int x;
    x := 0;
    x := f(x) + 1;
    print x;
}