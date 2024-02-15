int f(var int x) ::= x:= x+1;

null main () ::= {
    int x;
    x := f(1 + 2);
}