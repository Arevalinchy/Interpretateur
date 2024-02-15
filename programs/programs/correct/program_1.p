int toto(var int x) ::= 
x := (x + 1);

null main() ::= 
{
   int y;
   y := 1;
   print "premier\n";
   print(y);
   toto(y);
   print "\nsecond\n";
   print(y);
   print "\n";
}