include "vame.dfy"

class PolicyStoreLazy {
  ghost var rules: seq<Rule>
  ghost var Repr: set<object>

  // --- Required array representation ---
  var data: array<Rule>
  var count: nat   // number of valid entries in data[0..count]

  ghost predicate Valid()
    reads this, Repr, data
  {
    this in Repr &&
    data in Repr &&
    0 <= count <= data.Length &&
    rules == data[..count] 
  }

  constructor()
    ensures Valid() && fresh(Repr)
    ensures rules == []
  {
    rules := [];
    count := 0;

    var initialData := new Rule[1];
    data := initialData;
    Repr := {initialData};

    new;
    Repr := Repr + {this};
  }

  method add(r: Rule)
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures rules == old(rules) + [r]
  {
    if count == data.Length {
      var oldData := data;
      var newData := new Rule[count + 1];

      var i := 0;
      while i < count
        invariant 0 <= i <= count
        invariant forall j :: 0 <= j < i ==> newData[j] == oldData[j]
        modifies newData
      {
        newData[i] := oldData[i];
        i := i + 1;
      }
      newData[count] := r;
      data := newData;
      Repr := (Repr - {oldData}) + {newData};
    } else {
      data[count] := r;
    }

    count := count + 1;
    rules := rules + [r];
  }

  method remove(i: nat)
    requires Valid() && i < |rules|
    modifies Repr
    ensures  Valid()
    ensures  Repr == old(Repr)   // remove never allocates
    ensures  rules == old(rules[..i]) + old(rules[i+1..])
  {
    ghost var oldRules := rules;
    var j := i;
    while j < count - 1
      invariant i <= j <= count - 1
      invariant count == old(count)
      invariant rules == oldRules
      invariant forall k :: 0 <= k < i ==> data[k] == old(data[k])
      invariant forall k :: i <= k < j ==> data[k] == old(data[k+1])
      invariant forall k :: j < k < count ==> data[k] == old(data[k])
      modifies data
    {
      data[j] := data[j+1];
      j := j + 1;
    }
    count := count - 1;
    rules := oldRules[..i] + oldRules[i+1..];
}

  method lookup(q: Request) returns (d: Decision)
    requires Valid()
    ensures  d == eval(Pol(rules), q)
  {
    d := eval(Pol(data[..count]), q);
  }
}

class DecisionCacheLazy {
  ghost var Repr: set<object>
  var store: PolicyStoreLazy
  var hits: bv32
  var keys: array<Request>
  var values: array<Decision>
  var versions: array<nat>
  var size: nat                       // entries currently in cache
  var version: nat
  ghost var entries: map<Request, Decision>  // abstract view

  ghost predicate Valid()
    reads this, Repr, keys, store, store.Repr, store.data, values, versions
  {
    this in Repr 
    && store in Repr
    && keys in Repr
    && values in Repr
    && versions in Repr

    && store.Repr <= Repr && store.Valid()
    && store.Repr * {this, keys, values, versions} == {}

    // concrete cache is consistent
    && size <= CACHE_CAPACITY 
    && size <= keys.Length
    && size <= values.Length
    && size <= versions.Length

    && keys.Length == CACHE_CAPACITY 
    && values.Length == CACHE_CAPACITY 
    && versions.Length == CACHE_CAPACITY

    // ghost entries map matches concrete arrays
    // there is a key for every entry
    && (forall q :: q in entries ==> 
        exists i :: 0 <= i < size && keys[i] == q)
    // every value stored is also in map
    && (forall i :: 0 <= i < size ==> 
        keys[i] in entries && values[i] == entries[keys[i]])
    // concrete arrays have no duplicate keys (and maps too, by definition)
    && (forall i, j :: 0 <= i < j < size && 0 <= j < size ==> 
        keys[i] != keys[j])

    // results in cache are the same as policy store computed results
    && (forall i :: 0 <= i < size ==> 
      ((versions[i] == version) 
        ==> entries[keys[i]] == eval(Pol(store.rules), keys[i])))
    // versions in the versions array are at most version
    && (forall i :: 0 <= i < size ==>
      versions[i] <= version)
  }

  constructor(s: PolicyStoreLazy)
    requires s.Valid()
    ensures  Valid()
    ensures  store == s
    ensures  hits == 0
    ensures  fresh(Repr - s.Repr)
    ensures  keys.Length == CACHE_CAPACITY
    ensures  values.Length == CACHE_CAPACITY
    ensures  size == 0
    ensures  |entries| == 0
  {
    store    := s;
    hits     := 0;
    Repr     := {this} + s.Repr;
    keys     := new Request[CACHE_CAPACITY];
    values   := new Decision[CACHE_CAPACITY];
    versions := new nat[CACHE_CAPACITY];
    Repr     := Repr + {keys, values};
    Repr     := Repr + {versions};
    size     := 0;
    version  := 0;
    entries  := map[];
  }

  method lookup(q: Request) returns (d: Decision)
    requires Valid()
    modifies Repr, versions
    ensures  Valid()
    ensures  d == eval(Pol(store.rules), q)

    // hits
    ensures (exists i :: 0 <= i < old(size) && old(keys[i]) == q && old(versions[i]) == version)
      ==> hits == satInc(old(hits))
    ensures (exists i :: 0 <= i < old(size) && old(keys[i]) == q && old(versions[i]) != version)
      ==> hits == old(hits)
    ensures (forall i :: 0 <= i < old(size) ==> old(keys[i]) != q) 
      ==> hits == old(hits)

    // versions
  {
    var found := false;
    var leave := false;
    var index := -1;
    d := DenyD;

    // lookup in cache
    var i := 0;

    while i < size && !found && !leave
    decreases size - i
    invariant 0 <= i <= size
    invariant size <= keys.Length
    invariant size <= values.Length
    invariant store.Valid()
    invariant Valid()
    invariant hits == old(hits)
    invariant size == old(size)
    invariant forall j :: 0 <= j < size ==> keys[j] == old(keys[j])
    invariant forall j :: 0 <= j < size ==> versions[j] == old(versions[j])

    // found
    // if found, the key has already been scanned and has the current version
    invariant found ==> exists j :: 0 <= j < i && keys[j] == q && versions[j] == version
    // if found, the key has already been scanned but does not have the current version
    invariant leave ==> exists j :: 0 <= j < i && keys[j] == q && versions[j] != version
    // if not found or looked-up, the key has not been scanned
    invariant !found && !leave ==> forall j :: 0 <= j < i ==> keys[j] != q
    // if found, the return corresponds with the current cache entry
    invariant found ==> exists j :: 0 <= j < i && keys[j] == q && values[j] == d
    // if an outdated entry was found, d is the freshly evaluated decision
    invariant leave ==> d == eval(Pol(store.rules), q)
    
    // index
    invariant leave ==> exists j :: 0 <= j < i && keys[j] == q && versions[j] != version && index == j

    modifies {values}
    {
      if q == keys[i] {
        if versions[i] == version {
            found := true;
            d := values[i];
        } else {
            leave := true;
            d := store.lookup(q);
            index := i;
        }
      }
      i := i + 1;
    }

    // was found in cache
    if found {
      hits := satInc(hits);
    } 
    // outdated copy in cache
    else if leave {
        assert 0 <= index < size;
        assert keys[index] == q;
        values[index]   := d;
        versions[index] := version;
        entries := entries[q := d];
        assert forall j :: 0 <= j < size ==>
          keys[j] in entries && values[j] == entries[keys[j]];
    } 
    // no copy in cache
    else {
      d := store.lookup(q);
      if size < CACHE_CAPACITY 
      {
        keys[size] := q;
        values[size] := d;
        versions[size] := version;
        CoveragePreservedOnInsert(keys, size, q, d, entries);
        entries := entries[q := d];
        assert forall j :: 0 <= j < size + 1 ==>
          keys[j] in entries && values[j] == entries[keys[j]];
        size := size + 1;
      }
    }
  }

  lemma StoreDisjoint()
    requires Valid()
    ensures this !in store.Repr
    ensures keys !in store.Repr
    ensures values !in store.Repr
    ensures versions !in store.Repr
    ensures Valid()
  {
    assert this   !in (store.Repr * {this, keys, values, versions});
    assert keys   !in (store.Repr * {this, keys, values, versions});
    assert values !in (store.Repr * {this, keys, values, versions});
    if versions in store.Repr {
      assert versions in (store.Repr * {this, keys, values, versions});
      assert false;
    }
  }

  method addRule(r: Rule)
    requires Valid()
    modifies Repr
    ensures Valid()
    ensures store.rules == old(store.rules) + [r]
    ensures version == old(version) + 1
    ensures forall i :: 0 <= i < size ==> versions[i] < version
  { 
    StoreDisjoint();
    
    store.add(r);

    Repr := Repr + store.Repr;

    version := version + 1;
  }

  method removeRule(i: nat)
    requires Valid() && i < |store.rules|
    modifies Repr
    ensures  Valid()
    ensures  store.rules == old(store.rules[..i]) + old(store.rules[i+1..])
    ensures version == old(version) + 1
    ensures forall i :: 0 <= i < size ==> versions[i] < version
  {
    StoreDisjoint();

    store.remove(i);

    Repr := Repr + store.Repr;

    version := version + 1;
  }
}