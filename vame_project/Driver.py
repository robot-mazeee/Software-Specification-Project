"""
Driver.py — VAME test harness
Software Specification 26/27 (Python target)

Build and run:
    dafny build --target:py --output:vame vame.dfy
    mv vame-py vame          # Dafny 4.9 appends -py to the folder name
    python3 Driver.py

This file exercises eval, batchDecide, PolicyStore, and DecisionCache
against a fixed policy and checks every result. Expected output:

    === eval ===
    [PASS] alice  read  /reports                       AllowD
    [PASS] alice  read  /admin                         DenyD
    ...
    Results: N/N passed ✓

Compatibility: tested with Dafny 4.9, Python 3.10+.

Dafny 4.9 Python target layout (inside the renamed vame/ folder):
    module_.py          — all compiled Dafny code
    _dafny/__init__.py  — Dafny Python runtime (package, not a .py file)
    System_/            — Dafny system types
    __main__.py         — entry point (not used here)
"""

import sys
import os

_script_dir = os.path.dirname(os.path.abspath(__file__))
_build_dir  = os.path.join(_script_dir, "vame")   # renamed from vame-py

if not os.path.isdir(_build_dir):
    print("ERROR: build folder 'vame/' not found next to Driver.py.")
    print("Build first:")
    print("  dafny build --target:py --output:vame vame.dfy")
    print("  mv vame-py vame")
    sys.exit(1)

# vame/ must be on sys.path so that `import module_` and `import _dafny` resolve.
sys.path.insert(0, _build_dir)

# ---- import runtime ----------------------------------------------------------
try:
    from _dafny import SeqWithoutIsStrInference as DSeq, Array as DArray, CodePoint
except ImportError as e:
    print(f"ERROR: cannot import _dafny runtime: {e}")
    print("Make sure 'vame/' (the renamed build folder) is next to Driver.py.")
    sys.exit(1)

# ---- import compiled module --------------------------------------------------
try:
    from module_ import (
        default__,
        Request_Req,
        Matcher_AnyReq, Matcher_UserIs, Matcher_ActionIs,
        Matcher_ResourceIs, Matcher_And, Matcher_Or, Matcher_Not,
        Rule_Allow, Rule_Deny,
        Policy_Pol,
        PolicyStore,
        DecisionCache,
    )
except ImportError as e:
    print(f"ERROR: cannot import compiled module: {e}")
    sys.exit(1)


# ---------------------------------------------------------------------------
# Helpers: wrap Python strings as Dafny strings
# ---------------------------------------------------------------------------
# Dafny compiles `string` to a sequence of CodePoints, not plain Python str.
def dstr(s):
    return DSeq(map(CodePoint, s))

# ---------------------------------------------------------------------------
# Helpers: construct VAME datatypes
# ---------------------------------------------------------------------------
def req(user, action, resource):
    return Request_Req(dstr(user), dstr(action), dstr(resource))

def allow(matcher, priority):   return Rule_Allow(matcher, priority)
def deny(matcher, priority):    return Rule_Deny(matcher, priority)

def user_is(name):   return Matcher_UserIs(dstr(name))
def action_is(act):  return Matcher_ActionIs(dstr(act))
def resource_is(res):return Matcher_ResourceIs(dstr(res))
def any_req():       return Matcher_AnyReq()
def and_(l, r):      return Matcher_And(l, r)
def or_(l, r):       return Matcher_Or(l, r)
def not_(m):         return Matcher_Not(m)

def policy(rule_list):
    # The Dafny 4.9 codegen unwraps single-constructor datatypes: every compiled
    # function that takes a Policy receives the inner seq<Rule> directly.
    # Pass DSeq(rule_list) rather than Policy_Pol(DSeq(rule_list)).
    return DSeq(rule_list)

# Dafny 4.9 compiles Dafny functions as static methods on the `default__` class.
def eval_(p, q):         return default__.eval_(p, q)
def batch_decide(p, qs): return default__.batchDecide(p, qs)

# Dafny classes use a two-step construction:
#   obj = ClassName()    — allocates (sets all fields to None)
#   obj.ctor__(...)      — runs the Dafny constructor body
def make_store():
    s = PolicyStore()
    s.ctor__()
    return s

def make_cache(store):
    c = DecisionCache()
    c.ctor__(store)
    return c

# Decision predicates (Dafny Python datatypes expose `is_CtorName` properties).
def is_allow(d):    return getattr(d, "is_AllowD",  False)
def is_deny(d):     return getattr(d, "is_DenyD",   False)
def is_nomatch(d):  return getattr(d, "is_NoMatch", False)

def decision_name(d):
    if is_allow(d):   return "AllowD"
    if is_deny(d):    return "DenyD"
    if is_nomatch(d): return "NoMatch"
    return repr(d)

def expected_pred(name):
    return {"AllowD": is_allow, "DenyD": is_deny, "NoMatch": is_nomatch}[name]


# ---------------------------------------------------------------------------
# Test runner
# ---------------------------------------------------------------------------
passed = 0
failed = 0

def check(label, got, expected_name):
    global passed, failed
    pred = expected_pred(expected_name)
    ok   = pred(got)
    tag  = "PASS" if ok else "FAIL"
    print(f"  [{tag}] {label:<46} {decision_name(got)}")
    if not ok:
        print(f"         ^^^ expected {expected_name}")
        failed += 1
    else:
        passed += 1


# ---------------------------------------------------------------------------
# Fixed policy
#
#  0  Allow(UserIs("alice"),                   priority=10)
#  1  Deny (UserIs("bob"),                     priority=10)
#  2  Allow(ActionIs("read"),                  priority= 5)
#  3  Deny (ResourceIs("/admin"),              priority=20)
#  4  Allow(And(UserIs("carol"),read),         priority=15)
#  5  Deny (Not(UserIs("alice")),              priority= 1)   -- low priority
# ---------------------------------------------------------------------------

RULES = [
    allow(user_is("alice"),                             10),
    deny (user_is("bob"),                               10),
    allow(action_is("read"),                             5),
    deny (resource_is("/admin"),                        20),
    allow(and_(user_is("carol"), action_is("read")),    15),
    deny (not_(user_is("alice")),                        1),
]

POL = policy(RULES)


# ---------------------------------------------------------------------------
# 1. eval
# ---------------------------------------------------------------------------
print("\n=== eval ===")

check("alice  read  /reports",
      eval_(POL, req("alice","read","/reports")),  "AllowD")

# /admin Deny at 20 beats alice Allow at 10.
check("alice  read  /admin",
      eval_(POL, req("alice","read","/admin")),    "DenyD")

# Bob denied at 10; no Allow at >=10.
check("bob    write /reports",
      eval_(POL, req("bob","write","/reports")),   "DenyD")

# Carol+read Allow at 15; no Deny at >=15 for /reports.
check("carol  read  /reports",
      eval_(POL, req("carol","read","/reports")),  "AllowD")

# /admin Deny at 20 beats carol+read Allow at 15.
check("carol  read  /admin",
      eval_(POL, req("carol","read","/admin")),    "DenyD")

# dave write: rule 5 (Deny not-alice, prio=1) matches; rule 2 (Allow read)
# doesn't match action=write.  Deny at prio=1.
check("dave   write /reports",
      eval_(POL, req("dave","write","/reports")),  "DenyD")

# dave read: Allow(read,5) > Deny(not-alice,1).
check("dave   read  /reports",
      eval_(POL, req("dave","read","/reports")),   "AllowD")

# Empty policy.
check("alice  read  /reports  (empty policy)",
      eval_(policy([]), req("alice","read","/reports")),
      "NoMatch")

# Tie: Deny beats Allow at equal priority.
check("x/y/z  (Deny vs Allow, both prio=5, tie → DenyD)",
      eval_(policy([allow(any_req(),5), deny(any_req(),5)]),
            req("x","y","z")),
      "DenyD")


# ---------------------------------------------------------------------------
# 2. batchDecide
# ---------------------------------------------------------------------------
print("\n=== batchDecide ===")

batch = [
    req("alice","read", "/reports"),
    req("bob",  "write","/reports"),
    req("carol","read", "/reports"),
    req("dave", "write","/secret"),
]
expected_batch = ["AllowD","DenyD","AllowD","DenyD"]

darray = DArray(None, len(batch))
for i, r in enumerate(batch):
    darray[i] = r

out = batch_decide(POL, darray)
for i, exp in enumerate(expected_batch):
    check(f"batchDecide[{i}]", out[i], exp)


# ---------------------------------------------------------------------------
# 3. PolicyStore
# ---------------------------------------------------------------------------
print("\n=== PolicyStore ===")

store = make_store()

check("empty store: alice read /reports",
      store.lookup(req("alice","read","/reports")),
      "NoMatch")

store.add(RULES[0])   # Allow(alice, 10)
check("add Allow(alice,10) → alice read /x",
      store.lookup(req("alice","read","/x")),
      "AllowD")
check("add Allow(alice,10) → bob read /x",
      store.lookup(req("bob","read","/x")),
      "NoMatch")

store.add(RULES[3])   # Deny(/admin, 20)
check("add Deny(/admin,20) → alice read /admin",
      store.lookup(req("alice","read","/admin")),
      "DenyD")
check("add Deny(/admin,20) → alice read /reports",
      store.lookup(req("alice","read","/reports")),
      "AllowD")

store.add(RULES[1])   # Deny(bob, 10)
check("add Deny(bob,10) → bob write /x",
      store.lookup(req("bob","write","/x")),
      "DenyD")

# remove Deny(/admin,20); it is at index 1 (second rule added).
store.remove(1)
check("remove Deny(/admin,20) → alice read /admin",
      store.lookup(req("alice","read","/admin")),
      "AllowD")


# ---------------------------------------------------------------------------
# 4. DecisionCache
# ---------------------------------------------------------------------------
print("\n=== DecisionCache ===")

store2 = make_store()
for r in RULES:
    store2.add(r)

cache = make_cache(store2)

check("cache miss: alice read /reports",
      cache.lookup(req("alice","read","/reports")),
      "AllowD")
check("cache miss: bob write /reports",
      cache.lookup(req("bob","write","/reports")),
      "DenyD")
check("cache hit:  alice read /reports",
      cache.lookup(req("alice","read","/reports")),
      "AllowD")

# Adding a high-priority Deny for alice invalidates the cache.
cache.addRule(deny(user_is("alice"), 50))
check("after addRule Deny(alice,50): alice read /reports",
      cache.lookup(req("alice","read","/reports")),
      "DenyD")

# Remove the rule we just added (it's the last one: index = len(RULES)).
cache.removeRule(len(RULES))
check("after removeRule: alice read /reports",
      cache.lookup(req("alice","read","/reports")),
      "AllowD")


# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------
total = passed + failed
print(f"\n{'='*55}")
print(f"Results: {passed}/{total} passed", "✓" if failed == 0 else "✗")
if failed > 0:
    sys.exit(1)
