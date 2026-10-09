"""Check a student's JSON-line VAME client against one or more operation bundles.

Usage: python3 tests/check_client.py client.py tests/operations-small.json ...
"""

import json
from pathlib import Path
import subprocess
import sys


def check(client: str, bundle_path: str) -> bool:
    bundle = json.loads(Path(bundle_path).read_text(encoding="utf-8"))
    completed = subprocess.run(
        [sys.executable, client, bundle_path], text=True, capture_output=True
    )
    if completed.returncode != 0:
        print(f"[FAIL] {bundle_path}: client exited {completed.returncode}")
        if completed.stderr:
            print(completed.stderr.rstrip())
        return False
    try:
        result = json.loads(completed.stdout)
    except json.JSONDecodeError:
        print(f"[FAIL] {bundle_path}: stdout is not one JSON value")
        return False
    if result != {"decisions": bundle["expectedDecisions"]}:
        print(f"[FAIL] {bundle_path}: expected {bundle['expectedDecisions']!r}, got {result!r}")
        return False
    print(f"[PASS] {bundle_path}: {len(bundle['expectedDecisions'])} lookup decisions")
    return True


def main(argv: list[str]) -> int:
    if len(argv) < 3:
        print("usage: python3 tests/check_client.py client.py BUNDLE.json ...", file=sys.stderr)
        return 2
    passed = True
    for path in argv[2:]:
        if not check(argv[1], path):
            passed = False
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
