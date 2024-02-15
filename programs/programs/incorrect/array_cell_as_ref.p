null f(var int x) ::= 
x := x+1;

null main() ::=
{
    int tab[3];
    tab[0] := 0;
    tab[1] := 1;
    tab[2] := 2;
    print(tab[0]);
    print "\n";
    f(tab[0]);
    print(tab[0]);
    print "\n";
    int x;
    x := 0;
    print x;
    print "\n";
    f(x);
    print x;
    print "\n";
}