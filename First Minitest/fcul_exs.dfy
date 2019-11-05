method odd ( n: nat ) returns ( j : int )
    ensures j > n
    ensures j % 2 == 1
    ensures j == 1 + 2 * n
{
    var k := 0;
    j := 1;
    while k < n
        decreases n - k
        invariant j % 2 == 1 && k <= n && j == k * 2 + 1
    {
        k := k + 1;
        j := j + 2;
    }
}

method squareRoot ( n: nat ) returns ( r: nat )
    ensures r *r <= n < ( r + 1 ) * ( r + 1 )
{
    r := 0;
    var sqr := 1;
    while sqr <= n
        decreases n - sqr
        invariant sqr == (r+1) * (r+1) && r * r <= n
    {
        r := r + 1;
        sqr := sqr + 2 * r + 1;
    }
}

function method powerRec (n: nat) : nat
 decreases n
{
    if n == 0 then 1 else 2 * powerRec(n-1)
}

method power ( n: nat ) returns ( j : nat )
    ensures j == powerRec(n)
{
    var k := 0;
    j := 1;
    while k < n
        decreases n - k
        invariant j == powerRec(k) && k <= n
    {
        k := k + 1;
        j := 2 * j;
    }
}

method product (m: nat , n: nat ) returns ( res: nat )
    ensures res == m * n;
{
    var m1: nat := m; 
    res := 0;

    while m1 != 0 
        decreases m1 
        invariant res == n * ( m - m1)
    {
        var n1: nat := n;

        while n1 != 0 
            decreases n1
            invariant res == (m  * (m - m1)) + (n - n1)
        {
            res := res + 1;
            n1 := n1 - 1;
        }

        m1 := m1 - 1;
    }
}