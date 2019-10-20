// Finds a value 'x' in a sorted array 'a', and returns its index,
// or -1 if not found. 

// Checks if array 'a' is sorted.
predicate isSorted(a: array<int>)
    reads a
{
    forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

predicate notContains(a: array<int>, x: int)
    reads a
{
    x !in a[..]
}

method binarySearch(a: array<int>, x: int) returns (index: int)
    requires isSorted(a)
    ensures -1 <= index < a.Length
    ensures (index == -1 && notContains(a, x)) || (0 <= index < a.Length && x == a[index])
{   
    var low, high := 0, a.Length;
    while low < high 
        decreases high - low
        invariant 0 <= low <= high <= a.Length
        invariant forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
        invariant x in a[low..high] || notContains(a, x)
    {
        var mid := low + (high - low) / 2;
        if 
        {
            case a[mid]  < x => low := mid + 1;
            case a[mid]  > x => high := mid;
            case a[mid] == x => return mid;
        }
    }
    return -1;
}

// method Main(){

//     var a := new int[3];
//     a[0], a[1], a[2] := 1, 2, 3;

//     var i := binarySearch(a, 2);

//     assert(i == 1);

// }