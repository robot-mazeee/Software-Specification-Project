// =============================================================================
// VAME — Verified Authorization Mini-Engine
// Software Specification 26/27, Project 2
//
// CONVENTIONS
//
//   * The datatypes, `matches`, and the supplied selection core are fixed
//     infrastructure. Do not rename or remove anything here. You may add
//     helpers (functions, lemmas, predicates) freely.
//
//   * Items marked TODO are yours to fill in. Comments tying each TODO to a
//     handout section appear inline.
//
//   * The whole file verifies as written (all bodies are stubs). As you fill
//     items in, expect proofs that previously went through trivially to start
//     failing — that is the signal that your specifications are non-trivial.
//
//   * Tested on Dafny 4.9.
// =============================================================================


// ----- Provided datatypes ----------------------------------------------------

datatype Request = Req(user: string, action: string, resource: string)

datatype Matcher =
  | AnyReq
  | UserIs(name: string)
  | ActionIs(act: string)
  | ResourceIs(res: string)
  | And(left: Matcher, right: Matcher)
  | Or(left: Matcher, right: Matcher)
  | Not(inner: Matcher)

datatype Rule =
  | Allow(m: Matcher, priority: nat)
  | Deny(m: Matcher, priority: nat)

datatype Policy = Pol(rules: seq<Rule>)

datatype Decision = AllowD | DenyD | NoMatch

// A small Option<T> for the accumulator-style evaluator in 1.5. Defined
// locally rather than imported from Std.Wrappers so the starter has no
// external dependencies; if you prefer Std.Wrappers, replace this definition
// and the relevant uses below.

datatype Option<T> = None | Some(value: T)


// ----- Provided function: matcher semantics ----------------------------------
// You may consult `matches` freely. You do not need to prove anything about it.

function matches(m: Matcher, r: Request): bool
{
  match m
  case AnyReq         => true
  case UserIs(n)      => r.user == n
  case ActionIs(a)    => r.action == a
  case ResourceIs(rs) => r.resource == rs
  case And(l, rgt)    => matches(l, r) && matches(rgt, r)
  case Or(l, rgt)     => matches(l, r) || matches(rgt, r)
  case Not(inner)     => !matches(inner, r)
}


// Convenience: the priority of any rule (the field name is shared across
// constructors but Dafny does not currently project shared fields uniformly,
// so we expose it via a single helper).
function rulePriority(rl: Rule): nat
{
  match rl
  case Allow(_, p) => p
  case Deny(_, p)  => p
}

function ruleMatcher(rl: Rule): Matcher
{
  match rl
  case Allow(mr, _) => mr
  case Deny(mr, _)  => mr
}


// ----- Provided selection core ------------------------------------------------
//
// These definitions pin down the priority and tie-breaking semantics. They are
// supplied so that the project assesses specification and proof structure, not
// a large proof that a three-way maximum is associative. The supplied lemmas
// below are the interface students may use; do not modify them.

predicate beats(a: Rule, b: Rule)
{
  rulePriority(a) > rulePriority(b) ||
  (rulePriority(a) == rulePriority(b) && a.Deny? && b.Allow?)
}

function toDecision(opt: Option<Rule>): Decision
{
  match opt
  case None => NoMatch
  case Some(r) => if r.Allow? then AllowD else DenyD
}

function combineBest(a: Option<Rule>, b: Option<Rule>): Option<Rule>
{
  match a
  case None => b
  case Some(ra) =>
    match b
    case None => a
    case Some(rb) => if beats(ra, rb) then a else b
}

function bestRule(rules: seq<Rule>, q: Request): Option<Rule>
  decreases |rules|
{
  if rules == [] then None
  else
    var r0 := rules[0];
    var rest := bestRule(rules[1..], q);
    if !matches(ruleMatcher(r0), q) then rest
    else combineBest(Some(r0), rest)
}

// The following facts belong to the supplied selection library.
// Their implementations are hidden in this starter so they do not become
// accidental project tasks. You may call them in your proofs.
lemma combineBest_assoc(a: Option<Rule>, b: Option<Rule>, c: Option<Rule>)
  ensures toDecision(combineBest(combineBest(a, b), c)) ==
          toDecision(combineBest(a, combineBest(b, c)))
{
  assume {:axiom} false;
}

lemma bestRule_in_list(rules: seq<Rule>, q: Request)
  ensures bestRule(rules, q).Some? ==>
          exists i :: 0 <= i < |rules| &&
                      rules[i] == bestRule(rules, q).value &&
                      matches(ruleMatcher(rules[i]), q)
{
  assume {:axiom} false;
}

lemma bestRule_is_best(rules: seq<Rule>, q: Request)
  ensures (bestRule(rules, q) == None) <==>
          (forall i :: 0 <= i < |rules| ==> !matches(ruleMatcher(rules[i]), q))
  ensures bestRule(rules, q).Some? ==>
          forall i :: 0 <= i < |rules| &&
                      matches(ruleMatcher(rules[i]), q) ==>
                      !beats(rules[i], bestRule(rules, q).value)
{
  assume {:axiom} false;
}

lemma bestRule_append_nonmatching(rules: seq<Rule>, r: Rule, q: Request)
  requires !matches(ruleMatcher(r), q)
  ensures bestRule(rules + [r], q) == bestRule(rules, q)
{
  assume {:axiom} false;
}

lemma bestRule_append_dominated_decision(rules: seq<Rule>, r: Rule, q: Request)
  requires matches(ruleMatcher(r), q)
  requires bestRule(rules, q).Some?
  requires !beats(r, bestRule(rules, q).value)
  ensures toDecision(bestRule(rules + [r], q)) == toDecision(bestRule(rules, q))
{
  assume {:axiom} false;
}

lemma eval_allow_selects_allow(p: Policy, q: Request)
  requires eval(p, q) == AllowD
  ensures bestRule(p.rules, q).Some?
  ensures bestRule(p.rules, q).value.Allow?
{
  assume {:axiom} false;
}

lemma deny_not_beats_allow_is_lower(deny: Rule, allow: Rule)
  requires deny.Deny? && allow.Allow?
  requires !beats(deny, allow)
  ensures rulePriority(deny) < rulePriority(allow)
{
  assume {:axiom} false;
}


// =============================================================================
// PART 1 — Functional core (10 val.)
// =============================================================================


// -----------------------------------------------------------------------------
// 1.1 Evaluator [1.5 val.]
//
// Implement `eval(p, q)` following the priority semantics pinned by the handout
// (and re-stated here so this file is self-contained):
//
//   * Among the rules of `p` whose matcher matches `q`, the one with the
//     highest `priority` wins.
//   * If multiple rules match `q` at the same maximal priority, Deny wins
//     over Allow.
//   * If no rule matches `q`, the decision is `NoMatch`.
//
// The selection core above already provides `bestRule`. Your implementation
// should be a small wrapper that converts it with `toDecision`; the point is
// to connect the engine's public result to the supplied semantics.
// -----------------------------------------------------------------------------

function eval(p: Policy, q: Request): Decision
{
  // TODO (handout §1.1): implement the priority semantics above.
  NoMatch
}

lemma eval_total(p: Policy, q: Request)
  ensures eval(p, q) == AllowD || eval(p, q) == DenyD || eval(p, q) == NoMatch
{
  // TODO (handout §1.1): trivially provable once `eval` is total; Dafny
  // typically discharges it automatically.
}


// -----------------------------------------------------------------------------
// 1.2 Stability under low-priority additions [2 val.]
//
// State and prove: adding a rule that cannot beat the current winner does not
// change `eval(p, q)`. The handout guides the two necessary preconditions.
//
// Add the two requires clauses from the handout and a short English comment
// justifying each. Then case-split on whether r matches q and use the supplied
// append lemmas above.
// -----------------------------------------------------------------------------

lemma add_low_priority_stable(p: Policy, r: Rule, q: Request)
  // TODO (handout §1.2): design the precondition. The conclusion below is
  // intentionally not a tautology of `r.Deny?` or similar — the interesting
  // case is when the new rule's matcher does match `q`.
  // requires ...
  ensures eval(Pol(p.rules + [r]), q) == eval(p, q)
{
  // TODO (handout §1.2): prove.
}


// -----------------------------------------------------------------------------
// 1.3 Normalization to negation normal form [2.5 val.]
//
// A matcher is in NNF when `Not` only wraps an *atomic* matcher: `AnyReq`,
// `UserIs`, `ActionIs`, or `ResourceIs`. Define the predicate, implement
// `normalize`, and prove the two lemmas.
// -----------------------------------------------------------------------------

predicate isAtomic(m: Matcher)
{
  m.AnyReq? || m.UserIs? || m.ActionIs? || m.ResourceIs?
}

predicate isNNF(m: Matcher)
  decreases m
{
  match m
  case AnyReq | UserIs(_) | ActionIs(_) | ResourceIs(_) => true
  case And(l, r) => false //TODO
  case Or(l, r) => false //TODO
  case Not(inner) => false //TODO
}

// The lexicographic decreases pairs make the mutual calls terminating.
// Replace each deliberately incomplete right-hand side with the appropriate
// De Morgan / double-negation rewrite from the handout.
function normalizeNot(inner: Matcher): Matcher
  decreases inner, 0
{
  match inner
  case AnyReq => Not(AnyReq)
  case UserIs(n) => Not(UserIs(n))
  case ActionIs(a) => Not(ActionIs(a))
  case ResourceIs(r) => Not(ResourceIs(r))
  case And(l, r) => inner // TODO
  case Or(l, r) => inner  // TODO
  case Not(inner2) => inner // TODO: eliminate the double negation
}

function normalize(m: Matcher): Matcher
  decreases m, 1
{
  match m
  case AnyReq | UserIs(_) | ActionIs(_) | ResourceIs(_) => m
  case And(l, r) => m // TODO: normalize both children
  case Or(l, r) => m  // TODO: normalize both children
  case Not(inner) => m // TODO: call normalizeNot(inner)
}

lemma normalizeNot_sound(inner: Matcher, r: Request)
  ensures matches(normalizeNot(inner), r) == !matches(inner, r)
  decreases inner, 0
{
  assume {:axiom} false; // TODO: REMOVE this line!
  //Structural cases mirror normalizeNot.
  match inner {
    case And(l, rgt) => {}
    case Or(l, rgt)  => {}
    case Not(inner2) => {}
    case _ => {}
  }
}

lemma normalize_sound(m: Matcher, r: Request)
  ensures matches(normalize(m), r) == matches(m, r)
  decreases m, 1
{
  assume {:axiom} false; // TODO: REMOVE this line!
  //Structural cases mirror normalize.
    match m {
    case And(l, rgt) => {}
    case Or(l, rgt)  => {}
    case Not(inner2) => {}
    case _ => {}
    }
}

lemma normalizeNot_is_nnf(inner: Matcher)
  ensures isNNF(normalizeNot(inner))
  decreases inner, 0
{
  assume {:axiom} false; // TODO: REMOVE this line!
  // TODO: structural cases mirror normalizeNot.
    match inner {
    case And(l, r)   => {}
    case Or(l, r)    => {}
    case Not(inner2) => {}
    case _ => {}
  }
}

lemma normalize_is_nnf(m: Matcher)
  ensures isNNF(normalize(m))
  decreases m, 1
{
  assume {:axiom} false; // TODO: structural cases mirror normalize.
}


// -----------------------------------------------------------------------------
// 1.4 Witness lemma [2 val.]
//
// English statement (normative):
//   If `eval(p, q) == AllowD`, then there exists an index `i` into `p.rules`
//   such that:
//     (a) `p.rules[i]` is an Allow rule whose matcher matches `q`, AND
//     (b) no Deny rule of greater than or equal priority matches `q`.
//
// Translate this into a Dafny `lemma` with the appropriate `exists` /
// `forall` quantifiers. The grader evaluates both the faithfulness of your
// formal statement to the prose and the proof itself. A statement that is
// too weak (easy to prove but no longer captures the witness intuition)
// loses points.
// -----------------------------------------------------------------------------

lemma allow_has_witness(p: Policy, q: Request)
  requires eval(p, q) == AllowD
  // TODO (handout §1.4): state the existential conclusion described above.
  // The supplied facts above establish the winning rule's decision, membership,
  // and maximality. Write the stated existential / universal conclusion.
  // ensures ...
{
  var winner := bestRule(p.rules, q);
  eval_allow_selects_allow(p, q);
  bestRule_in_list(p.rules, q);
  bestRule_is_best(p.rules, q);
  // TODO: assert the appropriate universal with winner rule.
}


// -----------------------------------------------------------------------------
// 1.5 Accumulator-style evaluator [2 val.]
//
// Define a tail-recursive scan over the rules, threading the "best matching
// rule seen so far" through an accumulator. Prove it equivalent to `eval`.
// This rehearses the generalize-the-IH move from lecture 1: the naive
// induction hypothesis is too weak, and you must strengthen it to relate
// the accumulator to the *prefix already scanned*.
// -----------------------------------------------------------------------------

function evalAcc(rules: seq<Rule>, q: Request, best: Option<Rule>): Decision
{
  // TODO (handout §1.5): single left-to-right pass; `best` is the
  // highest-priority matching rule found so far (with Deny winning ties),
  // or `None` if no matching rule has yet been seen.
  NoMatch
}

// This is the intended strengthened induction hypothesis. `combineBest_assoc`
// is supplied above; you must prove this lemma after replacing evalAcc's body.
lemma evalAcc_eq_bestRule(rules: seq<Rule>, q: Request, best: Option<Rule>)
  ensures evalAcc(rules, q, best) ==
          toDecision(combineBest(best, bestRule(rules, q)))
  decreases |rules|
{
  assume {:axiom} false; // TODO (handout §1.5): induct on rules.
}

lemma evalAcc_eq_eval(p: Policy, q: Request)
  ensures evalAcc(p.rules, q, None) == eval(p, q)
{
  // TODO (handout §1.5): derive this from evalAcc_eq_bestRule with best := None.
}


// =============================================================================
// PART 2 — Imperative and object-oriented core (9 val.)
// =============================================================================


// -----------------------------------------------------------------------------
// 2.1 Batched decisions [2 val.]
//
// Imperative loop tying out[i] to eval(p, qs[i]). The loop invariant is yours
// to design; a hint is that it should talk about the prefix `qs[..i]`.
// -----------------------------------------------------------------------------

method batchDecide(p: Policy, qs: array<Request>) returns (out: array<Decision>)
  ensures fresh(out) && out.Length == qs.Length
  ensures forall i :: 0 <= i < qs.Length ==> out[i] == eval(p, qs[i])
{
  out := new Decision[qs.Length](_ => NoMatch);
  // TODO (handout §2.1): replace with a verified while-loop.
}


// -----------------------------------------------------------------------------
// 2.2 PolicyStore class [3 val.]
//
// Dynamic frames discipline: `Repr` set + `Valid()` predicate.
// Assessed representation: a resizable `array<Rule>`. A `seq<Rule>` field is
// NOT accepted. The optional linked-list bonus is a separate
// LinkedPolicyStore implementation; it does not replace this class.
// -----------------------------------------------------------------------------

class PolicyStore {
  ghost var rules: seq<Rule>
  ghost var Repr: set<object>

  // --- Required array representation ---
  // var data: array<Rule>
  // var count: nat   // number of valid entries in data[0..count]

  ghost predicate Valid()
    reads this, Repr
  {
    // TODO (handout §2.2): the standard dynamic-frames skeleton is
    //   this in Repr
    //   && (representation pieces are in Repr)
    //   && (concrete bounds: count <= data.Length, etc.)
    //   && (ghost <-> concrete: rules matches the chosen representation)
    this in Repr
  }

  constructor()
    ensures Valid() && fresh(Repr)
    ensures rules == []
  {
    rules := [];
    Repr := {this};
    // TODO (handout §2.2): initialise the concrete representation.
  }

  method add(r: Rule)
    requires Valid()
    modifies Repr
    ensures  Valid() && fresh(Repr - old(Repr))
    ensures  rules == old(rules) + [r]
  {
    assume {:axiom} false; // TODO (handout §2.2): append; may reallocate the backing array.
  }

  method remove(i: nat)
    requires Valid() && i < |rules|
    modifies Repr
    ensures  Valid()
    ensures  Repr == old(Repr)   // remove never allocates
    ensures  rules == old(rules[..i]) + old(rules[i+1..])
  {
    assume {:axiom} false; // TODO (handout §2.2): remove the i-th rule.
  }

  method lookup(q: Request) returns (d: Decision)
    requires Valid()
    ensures  d == eval(Pol(rules), q)
  {
    assume {:axiom} false; // TODO (handout §2.2): may either evaluate over rules directly, or do
    // an imperative scan with a loop invariant; both are acceptable.
    // Once you have a concrete representation, replace with e.g.:
    //   d := eval(Pol(data[..count]), q);
    d := NoMatch;
  }
}


// -----------------------------------------------------------------------------
// 2.3 DecisionCache class [3 val., + 1 val. bonus]
//
// Wraps a PolicyStore. Caches lookups up to a fixed capacity (1024). Tracks a
// bv32 saturating hit counter. Eager invalidation: every store mutation
// empties the cache.
//
// The skeleton below sketches the eager variant. The bonus lazy variant uses
// a `ghost var version: nat` on the store and re-validates on read.
// -----------------------------------------------------------------------------

const CACHE_CAPACITY: nat := 1024
const BV32_MAX: bv32 := 0xFFFFFFFF

function satInc(x: bv32): bv32
{
  if x == BV32_MAX then BV32_MAX else x + 1
}

// Provided helper for §2.3.  Call this after inserting q at keys[oldSz] and
// extending entries to oldEntries[q := d].  It proves the ``map entry has a
// concrete key slot'' direction of the cache representation invariant.
lemma CoveragePreservedOnInsert(
    keys: array<Request>, oldSz: nat, q: Request, d: Decision,
    oldEntries: map<Request, Decision>)
  requires oldSz < keys.Length
  requires keys[oldSz] == q
  requires q !in oldEntries
  requires forall q' :: q' in oldEntries ==> q' in keys[..oldSz]
  ensures forall q' {:trigger q' in (oldEntries[q := d])} ::
            q' in (oldEntries[q := d]) ==> q' in keys[..(oldSz + 1)]
{
  // The new used prefix is the old prefix followed by q.  Every entry in the
  // updated map is therefore either q itself or was already in oldEntries.
  assert keys[..(oldSz + 1)] == keys[..oldSz] + [q];
  forall q' {:trigger q' in (oldEntries[q := d])} |
      q' in (oldEntries[q := d])
    ensures q' in keys[..(oldSz + 1)]
  {
    if q' == q {
      // q is the final element of the extended prefix.
    }
    // Otherwise q' was in oldEntries and is covered by the precondition.
  }
}

class DecisionCache {
  ghost var Repr: set<object>
  var store: PolicyStore
  var hits: bv32
  // TODO (handout §2.3): concrete cache fields. For example,
  //   var keys: array<Request>
  //   var values: array<Decision>
  //   var size: nat                       // entries currently in cache
  //   ghost var entries: map<Request, Decision>  // abstract view

  ghost predicate Valid()
    reads this, Repr
  {
    // TODO (handout §2.3): the invariants of interest are
    //   this in Repr && store in Repr
    //   && store.Repr <= Repr && store.Valid()
    //   && (concrete cache is consistent: size <= CACHE_CAPACITY, etc.)
    //   && (ghost entries map matches concrete arrays)
    //   && (forall q :: q in entries ==> entries[q] == eval(Pol(store.rules), q))
    this in Repr && store in Repr
  }

  constructor(s: PolicyStore)
    requires s.Valid()
    ensures  Valid()
    ensures  store == s
    ensures  hits == 0
    ensures  fresh(Repr - s.Repr)
  {
    store := s;
    hits  := 0;
    Repr  := {this} + s.Repr;
    // TODO (handout §2.3): initialise concrete cache as empty.
  }

  method lookup(q: Request) returns (d: Decision)
    requires Valid()
    modifies Repr
    ensures  Valid()
    ensures  d == eval(Pol(store.rules), q)
    // TODO (handout §2.3): state the saturating hits post-condition.
    // E.g. `ensures hits == old(hits) || hits == satInc(old(hits))` plus a
    // tighter clause distinguishing miss-vs-hit if you want partial credit.
  {
    assume {:axiom} false; // TODO (handout §2.3): on hit, do `hits := satInc(hits);` and
    // return the cached value. On miss, call store.lookup(q) and populate the cache.
    d := store.lookup(q);
  }

  method addRule(r: Rule)
    requires Valid()
    modifies Repr
    ensures  Valid()
    ensures  store.rules == old(store.rules) + [r]
    // TODO (handout §2.3): post-condition stating the cache is empty after
    // this call. E.g. `ensures forall q :: q !in entries` once you have the
    // `entries` ghost map.
  {
    assume {:axiom} false; // TODO (handout §2.3): call store.add(r) and empty the cache.
    store.add(r);
  }

  method removeRule(i: nat)
    requires Valid() && i < |store.rules|
    modifies Repr
    ensures  Valid()
    ensures  store.rules == old(store.rules[..i]) + old(store.rules[i+1..])
    // TODO (handout §2.3): post-condition stating the cache is empty after
    // this call — symmetric to addRule.
    // ensures forall q :: q !in entries
  {
    assume {:axiom} false; // TODO (handout §2.3): call store.remove(i) and empty the cache.
    store.remove(i);
  }
}


// -----------------------------------------------------------------------------
// 2.4 Stress lemma [1 val.]
//
// State and prove: building a PolicyStore by adding rules rs[0], rs[1], ...
// in order and then calling `lookup(q)` returns `eval(Pol(rs), q)`.
//
// The proof should be short — most of the work is making the specifications
// of `add` and `lookup` strong enough that Dafny can compose them.
// -----------------------------------------------------------------------------

// TODO (handout §2.4): state and prove `stress_lemma`. The intended shape is:
//
//
// The proof is one line — the point is that your specifications of `PolicyStore`
// must be strong enough to make this compositionality fact fall out for free.
// If you need more than `{}` as a body, revisit your `Valid()` predicate and
// the postconditions of `add` / `lookup`.
