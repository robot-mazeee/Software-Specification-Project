include "vame.dfy"

class Node {
    var rule: Rule
    var next: Node?

    constructor(r: Rule)
        ensures rule == r && next == null
    {
        rule := r;
        next := null;
    }
}

class LinkedPolicyStore {
  ghost var rules: seq<Rule>
  ghost var Repr: set<object>
  ghost var nodes: seq<Node>

  var head: Node?
  var tail: Node?
  var count: nat

  ghost predicate Valid()
      reads this, Repr, tail
  {
      this in Repr &&
      count == |rules| == |nodes| &&
      (if nodes == [] then head == null && tail == null
       else head == nodes[0] && tail == nodes[|nodes|-1] && tail.next == null) &&
      (forall i, j :: 0 <= i < j < |nodes| ==> nodes[i] != nodes[j]) &&
      (forall i :: 0 <= i < |nodes| ==>
          nodes[i] in Repr &&
          rules[i] == nodes[i].rule &&
          (i + 1 == |nodes| || nodes[i].next == nodes[i+1]))
  }

  constructor()
      ensures Valid()
      ensures rules == []
      ensures count == 0
  {
      rules := [];
      nodes := [];
      head := null;
      tail := null;
      count := 0;
      Repr := {this};
  }

  method find(i: nat) returns (node: Node)
    requires Valid()
    requires i < count
    ensures node == nodes[i]
    ensures node in Repr
    ensures node.rule == rules[i]
    ensures node.next == (if i + 1 == count then null else nodes[i+1])
  {
    var current := head;
    var j: nat := 0;

    while j < i
        invariant j <= i
        invariant j < count
        invariant current == nodes[j]
        decreases i - j
    {
        current := current.next;
        j := j + 1;
    }
    node := current;
  }

  method add(r: Rule)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures rules == old(rules) + [r]
      ensures count == old(count) + 1
      ensures fresh(Repr - old(Repr))
  {
      var node := new Node(r);
      var oldCount := count;
      Repr := Repr + {node};

      if head == null {
        head := node;
        tail := node;
      } else {
        tail.next := node;
        tail := node;
      }

      count := count + 1;
      rules := rules + [r];
      nodes := nodes + [node];
  }

  method remove(i: nat)
      requires Valid()
      requires i < count
      modifies Repr
      ensures Valid()
      ensures rules == old(rules[..i]) + old(rules[i+1..])
      ensures count == old(count) - 1
      ensures Repr == old(Repr)
  {
      ghost var oldRules := rules;
      var oldCount := count;
      var current := head;
      var before: Node? := null;
      var j: nat := 0;

      while j < i
          invariant j <= i
          invariant current == nodes[j]
          invariant before == (if j == 0 then null else nodes[j-1])
          decreases i - j
      {
          before := current;
          current := current.next;
          j := j + 1;
      }

      var node := find(i);
      var after := node.next;

      if before == null {
          head := after;
      } else {
          before.next := after;
      }

      if i + 1 == oldCount {
          tail := before;
      }

      count := count - 1;
      rules := rules[..i] + rules[i+1..];
      nodes := nodes[..i] + nodes[i+1..];
  }

  method lookup(q: Request) returns (d: Decision)
      requires Valid()
      ensures d == eval(Pol(rules), q)
  {
      var data: seq<Rule> := [];
      var current := head;
      var i: nat := 0;

      while current != null
          invariant i <= count
          invariant current == (if i == count then null else nodes[i])
          invariant data == rules[..i]
          decreases count - i
      {
          data := data + [current.rule];
          current := current.next;
          i := i + 1;
      }

      assert data == rules;
      d := eval(Pol(data), q);
  }
}
