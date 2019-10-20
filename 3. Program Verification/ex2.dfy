predicate isSorted(a: array<int>)
    reads a
{
    forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}


// Sorts array 'a' using the insertion sort algorithm.
method insertionSort(a: array<int>)
    modifies a
    ensures isSorted(a)
    ensures multiset(a[..]) == multiset(old(a[..]))
{
    var i := 0;
    while i < a.Length 
        decreases a.Length - i
        invariant 0 <= i <= a.Length
        invariant a.Length == 0 || 0 <= i <= a.Length
        invariant forall l, r :: 0 <= l < r < i <= a.Length ==> a[l] <= a[r]
        invariant multiset(a[..]) == multiset(old(a[..]))
    {
        var j := i;
        while j > 0 && a[j-1] > a[j]
            decreases j
            invariant forall l, r :: (0 <= l < r <= i  && j != r) ==> a[l] <= a[r]
            invariant multiset(a[..]) == multiset(old(a[..]))
        {
            a[j-1], a[j] := a[j], a[j-1];
            j := j - 1;
        }
        i := i + 1;
    }
}
