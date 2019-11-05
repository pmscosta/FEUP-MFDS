method bubbleSort(a:array<int>)
  requires a.Length > 0
  ensures forall k:: forall l:: 0 <= k < l < a.Length ==> a[k] <= a[l]
  ensures multiset(a[..]) == multiset(old(a[..]))
  modifies a
{
  var i := a.Length - 1;
  while(i > 0)
    decreases i
    invariant i >= 0
    invariant forall k, l :: i < k < l < a.Length ==> a[k] <= a[l] //todos os elementos à direita do i estão ordenados
    invariant forall k, l :: 0 <= k <= i < l < a.Length ==> a[k] <= a[l] //todos os elementos à esquerda do i são inferiores dos da direira
  { 
    var j:int := 0;
    while (j < i)
        decreases i - j
        invariant j <= i
        invariant forall k, l :: i < k < l < a.Length ==> a[k] <= a[l]
        invariant forall k, l :: 0 <= k <= i < l < a.Length ==> a[k] <= a[l]
        invariant forall k :: i < k < a.Length ==> a[j] <= a[k] //o maior valor da esquerda é inferior a qualquer valor que já está na direita
        invariant forall k :: 0 <= k < j ==> a[k] <= a[j]  //a cada iteração do ciclo interior, o elemento maior é levado até ao fim, até à posição j
    {
      if (a[j] > a[j + 1]) {
        a[j], a[j+1] := a[j + 1], a[j];
      }
      j := j + 1;
    }
    i := i - 1;
  }
}

method Main(){

    var a := new int[5];
    a[0], a[1], a[2], a[3], a[4]:= 3, 1, 7, 4, 9; 

    assert(a[..] == [3, 1, 7, 4, 9]);
    bubbleSort(a); 
    print(a[0], a[1], a[2], a[3]);
    assert(a[..] == [1, 3, 4, 7, 9]);
}