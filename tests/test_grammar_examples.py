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
import argparse
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
    (";", "SEMICOLON"),
    ("(", "LPAREN"),
    (")", "RPAREN"),
    ("{", "LBRACE"),
    ("}", "RBRACE"),
    ("[", "LBRACKET"),
    ("]", "RBRACKET"),
]

RAW_FALLBACK = "__RAW__"


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
    is_literal: bool


@dataclass(frozen=True)
class TokenizationConfig:
    restricted_expr_contexts: frozenset[str]
    enforce_forbidden_tokens: bool = True
    enforce_have_guard: bool = True
    enforce_apply_with_guard: bool = True


STRICT_TOKENIZATION = TokenizationConfig(frozenset({"CALL", "APPLY"}))
CFG_COMPAT_TOKENIZATION = TokenizationConfig(
    frozenset(),
    enforce_forbidden_tokens=False,
    enforce_have_guard=False,
    enforce_apply_with_guard=False,
)


def build_token_specs(lexer_meta: Dict[str, Dict[str, object]]) -> List[TokenSpec]:
    specs: List[TokenSpec] = []
    priority = 0
    for name, spec in lexer_meta.items():
        pattern: str
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
            is_literal = True
        elif "pattern" in spec:
            pattern = str(spec["pattern"])
            is_literal = False
        else:
            priority += 1
            continue
        specs.append(
            TokenSpec(priority=priority, name=name, regex=re.compile(pattern), is_literal=is_literal)
        )
        priority += 1
    return specs


class TokenizationError(RuntimeError):
    pass


def split_specs(specs: Sequence[TokenSpec], lexer_meta: Dict[str, Dict[str, object]]
) -> Tuple[List[TokenSpec], List[TokenSpec]]:
    literal_specs: List[TokenSpec] = []
    pattern_specs: List[TokenSpec] = []
    for spec in specs:
        if spec.is_literal:
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

EXPR_START_TOKENS = {
    "CEQ",
    "COLON",
    "EQ",
    "IMPL",
    "LONGARROW",
    "HAVE",
    "GEN",
    "POSE",
    "CALL",
    "PROC",
    "INLINE",
    "RND",
    "REWRITE",
    "FIELD",
    "SMT",
    "SIM",
    "AUTO",
    "BYEQUIV",
    "BYPHOARE",
    "BYEHOARE",
    "MOVE",
    "APPLY",
    "EXACT",
    "WHILE",
    "ASYNC",
}
EXPR_END_TOKENS = {"DOT", "SEMICOLON", "CEQ", "COLON", "BY"}
EXPR_BREAK_TOKENS = set()

FORBIDDEN_EXPR_START_TOKENS = {
    "SLASH",
    "SLASHSLASH",
    "SLASHSLASHEQ",
    "SLASHSLASHTILDEQ",
    "SLASHSLASHSHARP",
    "SLASHSLASHGT",
    "SLASHSHARP",
    "SLASHEQ",
    "SLASHTILDEQ",
    "SLASHGT",
    "SLASHSLASHGT",
}

def tokenize_line(
    line: str,
    literal_specs: Sequence[TokenSpec],
    pattern_specs: Sequence[TokenSpec],
    structural_tokens: set[str],
    config: TokenizationConfig,
) -> List[str]:
    raw_tokens: List[str] = []
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
        matched_literal = False
        for literal, name in SYNTHETIC_LITERALS:
            if line.startswith(literal, pos):
                raw_tokens.append(name)
                pos += len(literal)
                matched_literal = True
                break
        if matched_literal:
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
                if spec.is_literal and lexeme and lexeme[-1].isalnum():
                    end = pos + span
                    if end < length and (line[end].isalnum() or line[end] == "_"):
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
            raw_tokens.append(RAW_FALLBACK)
            pos += 1
            continue
        raw_tokens.append(best[1])
        pos += best[2]

    if config.enforce_have_guard:
        arrow_tokens = {"RARROW", "LARROW", "LLARROW", "RRARROW"}
        for idx, tok in enumerate(raw_tokens):
            if tok != "HAVE":
                continue
            j = idx + 1
            while j < len(raw_tokens) and raw_tokens[j] in arrow_tokens:
                j += 1
            if j < len(raw_tokens) and raw_tokens[j] == "CEQ":
                raise TokenizationError("bare HAVE := without intro pattern is invalid")

    normalized: List[str] = []
    expr_mode = False
    expr_active = False
    expr_context: str | None = None
    expr_depth = 0
    for token in raw_tokens:
        if token in EXPR_END_TOKENS and expr_depth == 0:
            expr_mode = False
            expr_active = False
            expr_context = None
            expr_depth = 0
        elif token in EXPR_BREAK_TOKENS:
            expr_mode = False
            expr_active = False
            expr_context = None
            expr_depth = 0

        if (
            config.enforce_apply_with_guard
            and expr_context == "APPLY"
            and token == "WITH"
        ):
            raise TokenizationError("WITH clause is not supported in APPLY contexts")

        should_collapse = expr_mode or token == RAW_FALLBACK or token not in structural_tokens

        if should_collapse:
            if (
                config.enforce_forbidden_tokens
                and token == RAW_FALLBACK
                and expr_context in config.restricted_expr_contexts
            ):
                raise TokenizationError("unknown token encountered inside restricted expression")
            if (
                config.enforce_forbidden_tokens
                and expr_context in config.restricted_expr_contexts
                and token in FORBIDDEN_EXPR_START_TOKENS
                and not expr_active
            ):
                raise TokenizationError(f"invalid expression start token: {token}")
            expr_active = True
            if not expr_mode and (token == RAW_FALLBACK or token not in structural_tokens):
                expr_mode = True
            if token in {"LPAREN", "LBRACE", "LBRACKET"}:
                expr_depth += 1
            elif token in {"RPAREN", "RBRACE", "RBRACKET"} and expr_depth > 0:
                expr_depth -= 1
            mapped = "EXPR"
        else:
            mapped = token
            expr_active = False
            if not expr_mode:
                expr_depth = 0

        if not (mapped == "EXPR" and normalized and normalized[-1] == "EXPR"):
            normalized.append(mapped)

        if token in EXPR_START_TOKENS:
            expr_mode = True
            expr_active = False
            expr_context = token
            expr_depth = 0
    return normalized


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


def collect_structural_tokens(
    productions: Dict[str, List[Tuple[str, ...]]]
) -> set[str]:
    nonterminals = set(productions.keys())
    tokens: set[str] = set()
    for bodies in productions.values():
        for body in bodies:
            for symbol in body:
                if not symbol or symbol == "EXPR":
                    continue
                if symbol in nonterminals:
                    continue
                tokens.add(symbol)
    return tokens


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
    structural_tokens: set[str],
    tokenizer_config: TokenizationConfig,
) -> Tuple[
    bool,
    List[Tuple[int, str]],
    List[int],
    int,
    int,
    int,
]:
    errors: List[Tuple[int, str, str]] = []
    pass_lines: List[int] = []
    total = 0
    passed = 0
    unexpected = 0
    for idx, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        total += 1
        try:
            tokens = tokenize_line(
                line, literal_specs, pattern_specs, structural_tokens, tokenizer_config
            )
        except TokenizationError as exc:
            errors.append((idx, line, f"lex: {exc}"))
            continue
        if parser.parse(tokens):
            passed += 1
            pass_lines.append(idx)
        else:
            errors.append((idx, line, "parse error"))
            unexpected += 1
    compact_errors = [(lineno, msg) for lineno, _text, msg in errors]
    return len(errors) == 0, compact_errors, pass_lines, total, passed, unexpected


def main() -> None:
    arg_parser = argparse.ArgumentParser(description="Validate reduced EasyCrypt grammar.")
    arg_parser.add_argument(
        "--mode",
        choices=("strict", "cfg"),
        default="strict",
        help=(
            "strict = tokenizer guards enabled (default); "
            "cfg = grammar-only mode, emulating transformer decoders"
        ),
    )
    arg_parser.add_argument(
        "--skip-refresh",
        action="store_true",
        help="assume grammar artifacts are already up to date",
    )
    args = arg_parser.parse_args()

    if not args.skip_refresh:
        ensure_grammar()

    tokenizer_config = (
        STRICT_TOKENIZATION if args.mode == "strict" else CFG_COMPAT_TOKENIZATION
    )
    print(f"Tokenizer mode: {args.mode}")

    raw_meta = json.loads(RAW_GRAMMAR.read_text(encoding="utf-8"))
    lexer_meta = raw_meta.get("lexer", {})
    grammar_meta = json.loads(REDUCED_GRAMMAR.read_text(encoding="utf-8"))

    token_specs = build_token_specs(lexer_meta)
    literal_specs, pattern_specs = split_specs(token_specs, lexer_meta)
    productions, start = build_productions(grammar_meta)
    structural_tokens = collect_structural_tokens(productions)
    parser = EarleyParser(productions, start)

    scenarios = [
        ("good", GOOD_CASE, True),
        ("bad", BAD_CASE, False),
    ]

    overall_ok = True
    for label, path, expect_success in scenarios:
        ok, errors, pass_lines, total, passed_lines, unexpected = evaluate_file(
            path,
            parser,
            literal_specs,
            pattern_specs,
            structural_tokens,
            tokenizer_config,
        )
        behavioral_pass = ok if expect_success else not pass_lines
        overall_ok &= behavioral_pass
        status = "PASS" if behavioral_pass else "FAIL"
        print(f"[{status}] {label}: {path}")
        if total:
            print(f"    parsed {passed_lines}/{total} lines")
            if expect_success:
                failure_pct = ((total - passed_lines) / total) * 100.0
                metric = "not-parsed"
            else:
                failure_pct = (len(pass_lines) / total) * 100.0
                metric = "unexpectedly-parsed"
            print(f"    failure probability ({metric}): {failure_pct:.2f}%")
        if expect_success:
            failing_lines = [lineno for lineno, _ in errors]
            if failing_lines:
                print(f"    wrongfully-rejected line numbers: {failing_lines}")
        else:
            if pass_lines:
                print(f"    unexpectedly-parsing line numbers: {pass_lines}")

    if not overall_ok:
        sys.exit(1)


if __name__ == "__main__":
    main()

