"""Rename this file to client.py and complete run().

The program receives one operation-bundle JSON file and must print exactly one
JSON object of the form {"decisions": ["AllowD", ...]} on standard output.
Use only VameCache's public methods; do not import Dafny-generated modules.
"""

import json
import sys

from vame_api import VameCache


def run(bundle: dict) -> dict:
    cache = VameCache(bundle["initialRules"])
    decisions: list[str] = []

    for operation in bundle["operations"]:
        # TODO: dispatch "lookup", "add", and "remove" in their given order.
        # For every lookup, append cache.lookup(operation["request"]) to
        # decisions.  add/remove produce no output decisions.
        raise NotImplementedError("implement the operation dispatch")

    return {"decisions": decisions}


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: python3 client.py OPERATION_BUNDLE.json", file=sys.stderr)
        return 2
    with open(argv[1], encoding="utf-8") as source:
        result = run(json.load(source))
    print(json.dumps(result))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
