"""Stable Python API for the compiled VAME implementation.

Students should import only :class:`VameCache`; this module hides Dafny's
generated Python classes, strings, and datatype constructors.  Build
``vame.dfy`` first and rename Dafny 4.9's ``vame-py/`` output directory to
``vame/`` next to this file.
"""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from pathlib import Path
import sys
from typing import Any


JsonObject = Mapping[str, Any]


def _load_bindings() -> tuple[Any, ...]:
    """Load Dafny-generated classes, with a useful error if the build is absent."""
    build_dir = Path(__file__).resolve().parent / "vame"
    if not build_dir.is_dir():
        raise RuntimeError(
            "Compiled VAME code was not found. From project/, run:\n"
            "  dafny build --target:py --output:vame vame.dfy\n"
            "  mv vame-py vame"
        )
    if str(build_dir) not in sys.path:
        sys.path.insert(0, str(build_dir))
    try:
        from _dafny import CodePoint, SeqWithoutIsStrInference as DSeq
        from module_ import (
            DecisionCache,
            Matcher_ActionIs,
            Matcher_And,
            Matcher_AnyReq,
            Matcher_Not,
            Matcher_Or,
            Matcher_ResourceIs,
            Matcher_UserIs,
            PolicyStore,
            Request_Req,
            Rule_Allow,
            Rule_Deny,
        )
    except ImportError as exc:
        raise RuntimeError(
            "Could not import the compiled VAME module. Rebuild vame.dfy and "
            "ensure that the renamed vame/ directory is next to vame_api.py."
        ) from exc
    return (
        DSeq, CodePoint, DecisionCache, Matcher_ActionIs, Matcher_And,
        Matcher_AnyReq, Matcher_Not, Matcher_Or, Matcher_ResourceIs,
        Matcher_UserIs, PolicyStore, Request_Req, Rule_Allow, Rule_Deny,
    )


def _mapping(value: Any, label: str) -> JsonObject:
    if not isinstance(value, Mapping):
        raise ValueError(f"{label} must be a JSON object")
    return value


def _string(obj: JsonObject, key: str, label: str) -> str:
    value = obj.get(key)
    if not isinstance(value, str):
        raise ValueError(f"{label}.{key} must be a string")
    return value


def _dafny_string(value: str, bindings: tuple[Any, ...]) -> Any:
    dseq, codepoint = bindings[0], bindings[1]
    return dseq(map(codepoint, value))


def _build_matcher(raw: Any, bindings: tuple[Any, ...]) -> Any:
    matcher = _mapping(raw, "matcher")
    op = _string(matcher, "op", "matcher")
    if op == "AnyReq":
        return bindings[5]()
    if op == "UserIs":
        return bindings[9](_dafny_string(_string(matcher, "name", "matcher"), bindings))
    if op == "ActionIs":
        return bindings[3](_dafny_string(_string(matcher, "act", "matcher"), bindings))
    if op == "ResourceIs":
        return bindings[8](_dafny_string(_string(matcher, "res", "matcher"), bindings))
    if op == "And":
        return bindings[4](
            _build_matcher(matcher.get("left"), bindings),
            _build_matcher(matcher.get("right"), bindings),
        )
    if op == "Or":
        return bindings[7](
            _build_matcher(matcher.get("left"), bindings),
            _build_matcher(matcher.get("right"), bindings),
        )
    if op == "Not":
        return bindings[6](_build_matcher(matcher.get("inner"), bindings))
    raise ValueError(f"matcher.op is unsupported: {op!r}")


def _build_rule(raw: Any, bindings: tuple[Any, ...]) -> Any:
    rule = _mapping(raw, "rule")
    kind = _string(rule, "type", "rule")
    priority = rule.get("priority")
    if type(priority) is not int or priority < 0:
        raise ValueError("rule.priority must be a non-negative integer")
    matcher = _build_matcher(rule.get("matcher"), bindings)
    if kind == "Allow":
        return bindings[12](matcher, priority)
    if kind == "Deny":
        return bindings[13](matcher, priority)
    raise ValueError("rule.type must be 'Allow' or 'Deny'")


def _build_request(raw: Any, bindings: tuple[Any, ...]) -> Any:
    request = _mapping(raw, "request")
    return bindings[11](
        _dafny_string(_string(request, "user", "request"), bindings),
        _dafny_string(_string(request, "action", "request"), bindings),
        _dafny_string(_string(request, "resource", "request"), bindings),
    )


def _decision_name(decision: Any) -> str:
    if getattr(decision, "is_AllowD", False):
        return "AllowD"
    if getattr(decision, "is_DenyD", False):
        return "DenyD"
    if getattr(decision, "is_NoMatch", False):
        return "NoMatch"
    raise RuntimeError(f"VAME returned an unknown decision: {decision!r}")


class VameCache:
    """A stateful cache over an initial list of JSON-shaped policy rules.

    ``lookup`` returns one of ``AllowD``, ``DenyD``, or ``NoMatch``.  Rule and
    request dictionaries use the JSON schemas documented in the project
    handout.  ``add_rule`` and ``remove_rule`` preserve the compiled Dafny
    cache's eager-invalidation behavior.
    """

    def __init__(self, initial_rules: Sequence[JsonObject]) -> None:
        if isinstance(initial_rules, (str, bytes)) or not isinstance(initial_rules, Sequence):
            raise ValueError("initialRules must be a JSON array of rules")
        self._bindings = _load_bindings()
        store = self._bindings[10]()
        store.ctor__()
        for raw_rule in initial_rules:
            store.add(_build_rule(raw_rule, self._bindings))
        self._cache = self._bindings[2]()
        self._cache.ctor__(store)
        self._rule_count = len(initial_rules)

    @property
    def rule_count(self) -> int:
        """Number of rules currently held by the underlying policy store."""
        return self._rule_count

    def lookup(self, request: JsonObject) -> str:
        """Evaluate a JSON-shaped request through the verified cache."""
        return _decision_name(self._cache.lookup(_build_request(request, self._bindings)))

    def add_rule(self, rule: JsonObject) -> None:
        """Append a rule and eagerly invalidate cached decisions."""
        self._cache.addRule(_build_rule(rule, self._bindings))
        self._rule_count += 1

    def remove_rule(self, index: int) -> None:
        """Remove one rule by index and eagerly invalidate cached decisions."""
        if type(index) is not int or index < 0:
            raise ValueError("remove index must be a non-negative integer")
        if index >= self._rule_count:
            raise IndexError(f"remove index {index} is outside the policy")
        self._cache.removeRule(index)
        self._rule_count -= 1
