type T = int // to allow doing new T[capacity], but can be other type 
 
class {:autocontracts} Stack
{
    const elems: array<T>; // immutable (pointer)
    var size : nat; // used size
    
    predicate Valid()
        reads this
    {
        0 <= size <= elems.Length
    }

    constructor (capacity: nat)
        ensures elems.Length == capacity
        ensures isEmpty()
    {
        elems := new T[capacity];
        size := 0; 
    }
 
    predicate method isEmpty()
    {
        size == 0
    }
 
    predicate method isFull()
    {
        size == elems.Length
    }
 
    method push(x : T)
        requires !isFull()
        //ensures size == old(size) + 1
        //ensures x == top()
        ensures elems[..size] == old(elems[..size]) + [x]
    {
        elems[size] := x;
        size := size + 1;
    }
 
    function method top(): T
        requires !isEmpty()
        requires elems.Length > 0
        ensures top() == elems[size - 1]
        ensures elems[..size-1] + [top()] == elems[..size]
    {
         elems[size-1]
    }
    
    method pop() 
        requires size > 0
        ensures size == old(size) - 1
        ensures elems[..size] + [old(top())] == old(elems[..size])
        ensures elems[..size] == old(elems[..size-1])
    {
         size := size-1;
    }
}
 
// A simple test case.
method Main()
{
    var s := new Stack(3);
    assert s.isEmpty();
    s.push(1);
    s.push(2);
    s.push(3);
    assert s.top() == 3;
    assert s.isFull();
    s.pop();
    assert s.top() == 2;
    assert s.elems[..s.size] == [1,2]; //here to help 
    s.pop();
    assert s.top() == 1;
    print "top = ", s.top(), " \n";
}
