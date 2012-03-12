class Node
{
  var data: int;
  var next: Node;

  method Init(d: int)
    modifies this;
    ensures Valid();
    ensures data == d;
    ensures next == null;
  {
    data := d;
    next := null;
  }

  function Valid(): bool
    reads Repr();
    decreases Repr();
  {
    next != null ==> (this !in next.Repr() &&
      next.Repr() < Repr() && next.Valid())
  }

  function Repr(): set<Node>
  {
    {this} + if (next == null) then {} else next.Repr()
  }

  function Len(): int
    requires Valid();
    reads Repr();
    ensures 0 < Len();
  {
    if (next == null) then 1 else 1 + next.Len()
  }

  function Find(d: int): set<int>
    requires Valid();
    reads Repr();
    ensures (forall k :: k in Find(d) ==> 0 <= k < Len());
    ensures (forall i :: i in Find(d) ==> Get(this, i) == d);
  {
    FindHelper(d, 0)
  }

  function FindHelper(d: int, i: int): set<int>
    requires Valid();
    reads Repr();
    ensures (forall k :: k in FindHelper(d, i) ==> i <= k < i + Len());
    ensures (forall k :: k in FindHelper(d, i) ==> Get(this, k - i) == d);
    decreases Len();
  {
    if (data == d) then
      {i}
    else if (next != null) then
      next.FindHelper(d, i + 1)
    else
      {}
  }

  function Tail(): Node
    requires Valid();
    reads this;
  {
    next
  }

  static function Get(l: Node, i: int): int
    requires l != null && l.Valid();
    requires 0 <= i < l.Len();
    reads l.Repr();
    decreases i;
  {
    if (i == 0) then l.data else Get(l.next, i - 1)
  }

  static method Length(l: Node) returns (r: int)
    requires l != null && l.Valid();
    ensures r == l.Len();
    decreases l.Len();
  {
    if (l.next == null)
    {
      r := 1;
    }
    else
    {
      r := Length(l.next);
      r := r + 1;
    }
  }

  static method Equals(l1: Node, l2: Node) returns (r: bool)
    requires l1 != null && l2 != null && l1.Valid() && l2.Valid();
    ensures r ==> (l1.Len() == l2.Len() &&
      (forall i: int :: 0 <= i < l1.Len() ==> Get(l1, i) == Get(l2, i)));
    ensures (l1.Len() == l2.Len() &&
      (forall i: int :: 0 <= i < l1.Len() ==> Get(l1, i) == Get(l2, i))) ==> r;
    decreases l1.Len();
  {
    if (l1.data == l2.data)
    {
      if (l1.next == null && l2.next == null)
      {
        r := true;
      }
      else if (l1.next != null && l2.next != null)
      {
        r := Equals(l1.next, l2.next);
        assumed (l1.Len() == l2.Len() &&
          (forall i: int :: 0 <= i < l1.Len() ==>
             Get(l1, i) == Get(l2, i))) ==> r as a0;
      }
      else
      {
        assert l1.Len() != l2.Len();
        r := false;
      }
    }
    else
    {
      assert Get(l1, 0) != Get(l2, 0);
      r := false;
    }
  }

  static method Contains(d: int, l: Node) returns (r: bool)
    requires l != null && l.Valid();
    ensures r == (l.Find(d) != {});
    decreases l.Len();
  {
    if (l.data == d)
    {
      r := true;
    }
    else if (l.next == null)
    {
      r := false;
    }
    else
    {
      r := Contains(d, l.next);
      assert r == (l.next.Find(d) != {});
      assert r == (l.next.FindHelper(d, 0) != {});
      assumed r == (l.next.FindHelper(d, 1) != {}) as a0;
    }
  }

  static method Head(l: Node) returns (r: int)
    requires l != null && l.Valid() && 0 < l.Len();
    ensures r == Get(l, 0);
  {
    r := l.data;
  }

  static method Last(l: Node) returns (r: int)
    requires l != null && l.Valid();
    ensures r == Get(l, l.Len() - 1);
    decreases l.Len();
  {
    if (l.next == null)
    {
      r := l.data;
    }
    else
    {
      r := Last(l.next);
    }
  }

  static method SkipHead(l: Node) returns (r: Node)
    requires l != null && l.Valid();
    ensures r == l.Tail();
  {
    r := l.next;
  }

  static method Prepend(d: int, l: Node) returns (r: Node)
    requires l != null && l.Valid();
    ensures r != null && fresh(r) && r.Valid();
    ensures Get(r, 0) == d;
    ensures r.Tail() == l;
    ensures r.Len() == l.Len() + 1;
  {
    r := new Node.Init(d);
    r.next := l;
  }

  static method Append(d: int, l: Node)
    requires l != null && l.Valid();
    modifies l.Repr();
    ensures l.Valid();
    ensures l.Len() == old(l.Len() + 1);
    // ensures fresh(l.Repr() - old(l.Repr()));
    // ensures forall i :: 0 <= i < l.Len() - 1 ==> Get(l, i) == old(Get(l, i));
    ensures Get(l, l.Len() - 1) == d;
    decreases l.Len();
  {
    if (l.next == null)
    {
      l.next := new Node.Init(d);
    }
    else
    {
      Append(d, l.next);
    }
  }

  static method Concat(l1: Node, l2: Node)
    requires l1 != null && l2 != null && l1.Valid() && l2.Valid();
    requires l1.Repr() !! l2.Repr();
    modifies l1.Repr();
    ensures l1.Valid();
    ensures l1.Repr() == old(l1.Repr() + l2.Repr());
    // ensures forall i :: 0 <= i < old(l1.Len()) ==>
    //   Get(l1, i) == old(Get(l1, i));
    // ensures forall i :: old(l1.Len()) <= i < l1.Len() ==>
    //   Get(l1, i) == old(Get(l2, i));
    decreases l1.Len();
  {
    if (l1.next == null)
    {
      l1.next := l2;
    }
    else
    {
      Concat(l1.next, l2);
    }
  }

  static method Clone(l: Node) returns (r: Node)
    requires l != null && l.Valid();
    ensures r != null && r.Valid();
    ensures fresh(r.Repr());
    ensures l.Len() == r.Len();
    free ensures forall i :: 0 <= i < l.Len() ==> Get(l, i) == Get(r, i);
    decreases l.Len();
  {
    var c := new Node.Init(l.data);
    var tmp: Node;
    if (l.next != null)
    {
      tmp := Clone(l.next);
      c.next := tmp;
    }
    assert forall i :: 0 <= i < l.Len() ==> Get(l, i) == Get(c, i);
    r := c;
  }

  static method Reverse(l: Node) returns (r: Node)
    requires l != null && l.Valid();
    modifies l.Repr();
    ensures r != null && r.Valid();
    ensures old(l.Len()) == r.Len();
  {
    var current := l.next;
    r := l;
    r.next := null;
    var tmp: Node;
    while (current != null)
      invariant r != null && r.Valid();
      decreases *;
    {
      tmp := current.next;
      current.next := r;
      r := current;
      current := tmp;
    }
  }
}
