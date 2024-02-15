int fibo(var int[] tab,int num) ::= 
{
   if (tab[num] = -1) then
    {
       int res;
       res := (fibo(tab,(num - 1)) + fibo(tab,(num - 2)));
       tab[num] := res;
       return res;
    }
   else
    return tab[num];
}

null main() ::= 
{
   int tab[11];
   int count;
   tab[0] := 0;
   tab[1] := 1;
   count := 2;
   while (count < tab.size)
    {
       tab[count] := -1;
       count := (count + 1);
    }
   fibo(tab,10);
   count := 0;
   while (count < tab.size)
    {
       print(count);
       print " : ";
       print(tab[count]);
       print "\n";
       count := (count + 1);
    }
   return;
}