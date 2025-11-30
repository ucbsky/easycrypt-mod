#!/usr/bin/env python3
"""
Quick sanity test that exercises the reduced tactic grammar on curated examples.

The script:
  1. Regenerates the normalized grammar artifacts.
  2. Builds a lightweight Earley parser directly from `grammar_reduced_expr.json`.
  3. Tokenizes each input line using the lexer definitions in `grammar_raw.json`.
  4. Parses every line of `grammar_examples/good.ec` (should succeed).
  5. Confirms that at least one line of `grammar_examples/bad.ec` fails to parse.
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

PROJECT_ROOT = Path(__file__).resolve().parents[1]
OUT_DIR = PROJECT_ROOT / "out"

RAW_GRAMMAR = OUT_DIR / "grammar_raw.json"
REDUCED_GRAMMAR = OUT_DIR / "grammar_reduced_expr.json"

GOOD_CASE = PROJECT_ROOT / "grammar_examples" / "good.ec"
BAD_CASE = PROJECT_ROOT / "grammar_examples" / "bad.ec"

SYNTHETIC_LITERALS: List[Tuple[str, str]] = [
    (".", "DOT"),
]


def ensure_grammar() -> None:
    """Run the inspector to refresh reduced grammar artifacts."""
    subprocess.run(
        [sys.executable, str(OUT_DIR / "inspect_raw_grammar.py")],
        check=True,
    )


def escape_literal(lit: str) -> str:
    return re.escape(lit)


@dataclass(frozen=True)
class TokenSpec:
    priority: int
    name: str
    regex: re.Pattern[str]


def build_token_specs(lexer_meta: Dict[str, Dict[str, object]]) -> List[TokenSpec]:
    specs: List[TokenSpec] = []
    priority = 0
    for name, spec in lexer_meta.items():
        pattern: str
        is_literal = False
        if "literals" in spec:
            literals = spec["literals"] or []
            literals_sorted = sorted(
                (str(l) for l in literals),
                key=len,
                reverse=True,
            )
            if not literals_sorted:
                priority += 1
                continue
            pattern = "|".join(escape_literal(lit) for lit in literals_sorted)
        elif "pattern" in spec:
            pattern = str(spec["pattern"])
        else:
            priority += 1
            continue
        specs.append(TokenSpec(priority=priority, name=name, regex=re.compile(pattern)))
        priority += 1
    return specs


class TokenizationError(RuntimeError):
    pass


def split_specs(specs: Sequence[TokenSpec], lexer_meta: Dict[str, Dict[str, object]]
) -> Tuple[List[TokenSpec], List[TokenSpec]]:
    literal_specs: List[TokenSpec] = []
    pattern_specs: List[TokenSpec] = []
    for spec in specs:
        meta = lexer_meta.get(spec.name, {})
        if meta.get("literals"):
            literal_specs.append(spec)
        else:
            pattern_specs.append(spec)
    return literal_specs, pattern_specs


IDENT_PRIORITY = {
    "LIDENT": 0,
    "UIDENT": 1,
    "TIDENT": 2,
    "MIDENT": 3,
}


def tokenize_line(
    line: str,
    literal_specs: Sequence[TokenSpec],
    pattern_specs: Sequence[TokenSpec],
) -> List[str]:
    tokens: List[str] = []
    pos = 0
    length = len(line)
    while pos < length:
        ch = line[pos]
        if ch.isspace():
            pos += 1
            continue
        if ch == "(" and pos + 1 < length and line[pos + 1] == "*":
            end = line.find("*)", pos + 2)
            if end == -1:
                raise TokenizationError("unterminated comment")
            pos = end + 2
            continue
        synthetic_hit = False
        for literal, name in SYNTHETIC_LITERALS:
            if line.startswith(literal, pos):
                tokens.append(name)
                pos += len(literal)
                synthetic_hit = True
                break
        if synthetic_hit:
            continue

        best: Tuple[int, str, int] | None = None
        for spec_group in (literal_specs, pattern_specs):
            for spec in spec_group:
                match = spec.regex.match(line, pos)
                if not match:
                    continue
                lexeme = match.group(0)
                span = len(lexeme)
                if spec.name == "MIDENT":
                    trimmed_span = len(lexeme.rstrip("."))
                    if trimmed_span == 0:
                        continue
                    span = trimmed_span
                if span == 0:
                    continue
                if best is None or span > best[2]:
                    best = (spec.priority, spec.name, span)
                    continue
                if span == best[2]:
                    current_rank = IDENT_PRIORITY.get(spec.name, float("inf"))
                    best_rank = IDENT_PRIORITY.get(best[1], float("inf"))
                    if current_rank != best_rank:
                        if current_rank < best_rank:
                            best = (spec.priority, spec.name, span)
                    elif spec.priority < best[0]:
                        best = (spec.priority, spec.name, span)
            if best:
                break
        if best is None:
            snippet = line[pos : pos + 20]
            raise TokenizationError(f"unknown token near {snippet!r}")
        tokens.append(best[1])
        pos += best[2]
    return tokens


def build_productions(grammar_meta: Dict[str, List[Dict[str, object]]]) -> Tuple[
    Dict[str, List[Tuple[str, ...]]], str
]:
    productions: Dict[str, List[Tuple[str, ...]]] = {}
    for head, prods in grammar_meta.items():
        bodies: List[Tuple[str, ...]] = []
        for prod in prods:
            symbols = tuple(prod.get("body_symbols") or [])
            bodies.append(symbols)
        productions[head] = bodies
    start_symbol = "Line"
    productions["_START_"] = [(start_symbol,)]
    return productions, "_START_"


@dataclass(frozen=True)
class Item:
    head: str
    body: Tuple[str, ...]
    dot: int
    origin: int


class EarleyParser:
    def __init__(self, productions: Dict[str, List[Tuple[str, ...]]], start: str):
        self.productions = productions
        self.start = start
        self.nonterminals = set(productions.keys())

    def parse(self, tokens: Sequence[str]) -> bool:
        n = len(tokens)
        chart: List[set[Item]] = [set() for _ in range(n + 1)]
        start_body = self.productions[self.start][0]
        start_item = Item(self.start, start_body, 0, 0)
        chart[0].add(start_item)

        for i in range(n + 1):
            changed = True
            while changed:
                changed = False
                snapshot = list(chart[i])
                for item in snapshot:
                    if item.dot < len(item.body):
                        sym = item.body[item.dot]
                        if sym in self.nonterminals:
                            for prod in self.productions.get(sym, []):
                                new_item = Item(sym, prod, 0, i)
                                if new_item not in chart[i]:
                                    chart[i].add(new_item)
                                    changed = True
                        else:
                            if i < n and tokens[i] == sym:
                                advanced = Item(item.head, item.body, item.dot + 1, item.origin)
                                if advanced not in chart[i + 1]:
                                    chart[i + 1].add(advanced)
                    else:
                        origin_snapshot = list(chart[item.origin])
                        for origin_item in origin_snapshot:
                            if (
                                origin_item.dot < len(origin_item.body)
                                and origin_item.body[origin_item.dot] == item.head
                            ):
                                completed = Item(
                                    origin_item.head,
                                    origin_item.body,
                                    origin_item.dot + 1,
                                    origin_item.origin,
                                )
                                if completed not in chart[i]:
                                    chart[i].add(completed)
                                    changed = True

        accepting = Item(self.start, start_body, len(start_body), 0)
        return accepting in chart[n]


def evaluate_file(
    path: Path,
    parser: EarleyParser,
    literal_specs: Sequence[TokenSpec],
    pattern_specs: Sequence[TokenSpec],
) -> Tuple[bool, List[Tuple[int, str, str]]]:
    errors: List[Tuple[int, str, str]] = []
    for idx, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        try:
            tokens = tokenize_line(line, literal_specs, pattern_specs)
        except TokenizationError as exc:
            errors.append((idx, line, f"lex: {exc}"))
            continue
        if not parser.parse(tokens):
            errors.append((idx, line, "parse error"))
    return len(errors) == 0, errors


def main() -> None:
    ensure_grammar()

    raw_meta = json.loads(RAW_GRAMMAR.read_text(encoding="utf-8"))
    lexer_meta = raw_meta.get("lexer", {})
    grammar_meta = json.loads(REDUCED_GRAMMAR.read_text(encoding="utf-8"))

    token_specs = build_token_specs(lexer_meta)
    literal_specs, pattern_specs = split_specs(token_specs, lexer_meta)
    productions, start = build_productions(grammar_meta)
    parser = EarleyParser(productions, start)

    scenarios = [
        ("good", GOOD_CASE, True),
        ("bad", BAD_CASE, False),
    ]

    overall_ok = True
    for label, path, expect_success in scenarios:
        ok, errors = evaluate_file(path, parser, literal_specs, pattern_specs)
        passed = ok if expect_success else not ok
        overall_ok &= passed
        status = "PASS" if passed else "FAIL"
        print(f"[{status}] {label}: {path}")
        if errors:
            for lineno, text, msg in errors[:5]:
                print(f"    line {lineno}: {text}")
                print(f"      {msg}")

    if not overall_ok:
        sys.exit(1)


if __name__ == "__main__":
    main()

