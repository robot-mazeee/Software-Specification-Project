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
        op = operation["op"]

        if op == "lookup":
            decisions.append(cache.lookup(operation["request"]))

        elif op == "add":
            cache.add_rule(operation["rule"])

        elif op == "remove":
            cache.remove_rule(operation["index"])

        else:
            raise ValueError("Invalid operation: " + op)

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
