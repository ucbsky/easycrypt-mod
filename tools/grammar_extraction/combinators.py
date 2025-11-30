"""
Helpers for expanding Menhir combinators such as plist/rlist/loc/paren.

This module currently provides placeholder utilities; the heavy lifting will
be implemented iteratively as we discover new patterns in the EasyCrypt parser.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Iterable, List


LIST_CALL_RE = re.compile(r"(?P<name>[pr]list[0-9]?)\((?P<body>[^)]+)\)")


@dataclass
class CombinatorExpansion:
    original: str
    replacements: List[str]


def strip_bindings(sequence: str) -> List[str]:
    """Remove Menhir bindings like `x=expr` to get bare symbol names."""

    symbols: List[str] = []
    for token in sequence.split():
        if "=" in token:
            token = token.split("=", 1)[1]
        symbols.append(token)
    return symbols


def expand_lists(symbol: str) -> List[str]:
    """
    Recognize rlist/plist helpers and expand them into helper nonterminals.

    For now this simply returns the original symbol; full expansion will be
    implemented in a later iteration.
    """

    match = LIST_CALL_RE.match(symbol)
    if not match:
        return [symbol]
    return [symbol]  # placeholder

