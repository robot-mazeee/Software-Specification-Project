"""
run_tests.py — JSON-driven VAME test runner
Software Specification 26/27

Usage:
    python tests/run_tests.py tests/small.json tests/medium.json

Each JSON file has the schema:
  {
    "description": "...",
    "policy": [ {"type": "Allow"|"Deny", "matcher": <matcher>, "priority": N}, ... ],
    "cases":  [ {"user":"...", "action":"...", "resource":"...",
                 "expected":"AllowD"|"DenyD"|"NoMatch", "note":"..."}, ... ]
  }

Matcher schema (recursive):
  {"op": "AnyReq"}
  {"op": "UserIs",     "name": "..."}
  {"op": "ActionIs",   "act":  "..."}
  {"op": "ResourceIs", "res":  "..."}
  {"op": "And",  "left": <matcher>, "right": <matcher>}
  {"op": "Or",   "left": <matcher>, "right": <matcher>}
  {"op": "Not",  "inner": <matcher>}
"""

import sys
import os
import json

# ---- locate compiled module ---------------------------------------------------
# Dafny 4.9 output layout: vame/ contains module_.py and _dafny/ package.
# Add the build folder to sys.path so both resolve.
_project_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
_build_dir   = os.path.join(_project_dir, "vame")
if os.path.isdir(_build_dir):
    sys.path.insert(0, _build_dir)

try:
    from _dafny import SeqWithoutIsStrInference as DSeq, CodePoint
    from module_ import (
        default__,
        Matcher_AnyReq, Matcher_UserIs, Matcher_ActionIs,
        Matcher_ResourceIs, Matcher_And, Matcher_Or, Matcher_Not,
        Rule_Allow, Rule_Deny,
        Request_Req,
    )
except ImportError as e:
    print(f"ERROR: cannot import compiled module: {e}")
    print("Build first:")
    print("  dafny build --target:py --output:vame vame.dfy")
    print("  mv vame-py vame")
    sys.exit(1)

def dstr(s):
    return DSeq(map(CodePoint, s))


# ---------------------------------------------------------------------------
# Build matchers and rules from JSON
# ---------------------------------------------------------------------------

def build_matcher(m):
    op = m["op"]
    if op == "AnyReq":      return Matcher_AnyReq()
    if op == "UserIs":      return Matcher_UserIs(dstr(m["name"]))
    if op == "ActionIs":    return Matcher_ActionIs(dstr(m["act"]))
    if op == "ResourceIs":  return Matcher_ResourceIs(dstr(m["res"]))
    if op == "And":         return Matcher_And(build_matcher(m["left"]),
                                               build_matcher(m["right"]))
    if op == "Or":          return Matcher_Or(build_matcher(m["left"]),
                                              build_matcher(m["right"]))
    if op == "Not":         return Matcher_Not(build_matcher(m["inner"]))
    raise ValueError(f"Unknown matcher op: {op}")

def build_rule(r):
    m = build_matcher(r["matcher"])
    p = r["priority"]
    if r["type"] == "Allow": return Rule_Allow(m, p)
    if r["type"] == "Deny":  return Rule_Deny(m, p)
    raise ValueError(f"Unknown rule type: {r['type']}")

def build_policy(rules_json):
    rules = [build_rule(r) for r in rules_json]
    # Dafny 4.9 codegen unwraps Policy — pass the raw rules seq, not Policy_Pol.
    return DSeq(rules)

def decision_name(d):
    if getattr(d, "is_AllowD",  False): return "AllowD"
    if getattr(d, "is_DenyD",   False): return "DenyD"
    if getattr(d, "is_NoMatch", False): return "NoMatch"
    return repr(d)



# ---------------------------------------------------------------------------
# Run one test file
# ---------------------------------------------------------------------------

def run_file(path):
    with open(path) as f:
        data = json.load(f)

    desc   = data.get("description", path)
    policy = build_policy(data["policy"])
    cases  = data["cases"]

    print(f"\n{'='*60}")
    print(f"  {desc}")
    print(f"  {len(cases)} cases")
    print(f"{'='*60}")

    ok = 0
    err = 0
    for i, c in enumerate(cases):
        q   = Request_Req(dstr(c["user"]), dstr(c["action"]), dstr(c["resource"]))
        got = default__.eval_(policy, q)
        gname = decision_name(got)
        exp   = c["expected"]
        note  = c.get("note", "")
        if gname == exp:
            print(f"  [PASS] #{i:02d} {c['user']:<10} {c['action']:<8} {c['resource']:<15}  {gname}")
            ok += 1
        else:
            print(f"  [FAIL] #{i:02d} {c['user']:<10} {c['action']:<8} {c['resource']:<15}  got={gname} expected={exp}  ({note})")
            err += 1

    print(f"  --- {ok}/{ok+err} passed ---")
    return err


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    files = sys.argv[1:] or ["tests/small.json", "tests/medium.json"]
    total_errors = 0
    for path in files:
        if not os.path.exists(path):
            print(f"WARNING: test file not found: {path}")
            continue
        total_errors += run_file(path)

    print()
    if total_errors == 0:
        print("All tests passed ✓")
    else:
        print(f"{total_errors} test(s) FAILED ✗")
        sys.exit(1)
