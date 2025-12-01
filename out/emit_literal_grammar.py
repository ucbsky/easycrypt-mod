#!/usr/bin/env python3
"""
Emit an EBNF that maps every token name in the reduced grammar to concrete
character literals (or small regex-style expressions) so `transformers-cfg`
sees real terminals instead of the Menhir token identifiers.

The script walks `grammar_reduced_expr.json`, identifies the terminal symbols,
and then expands each token using the literal/pattern definitions from
`grammar_raw.json`. We sprinkle optional whitespace (`WS_OPT`) between every
symbol in each production so raw EasyCrypt source—with arbitrary indentation or
spacing—matches the grammar directly.

Tokens that have no literal or regex definition fall back to synthetic
placeholders (`__token__`). Run with `--strict` if you prefer the script to
fail instead of producing placeholders.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Set, Tuple

PROJECT_ROOT = Path(__file__).resolve().parents[1]
OUT_DIR = PROJECT_ROOT / "out"

DEFAULT_GRAMMAR = OUT_DIR / "grammar_reduced_expr.json"
DEFAULT_LEXER = OUT_DIR / "grammar_raw.json"
DEFAULT_OUTPUT = OUT_DIR / "grammar_reduced_expr_literals.ebnf"

PUNCTUATION_OVERRIDES: Dict[str, List[str]] = {
    "AMP": ["&"],
    "AT": ["@"],
    "COLON": [":"],
    "COMMA": [","],
    "DOT": ["."],
    "DOTDOT": [".."],
    "EQ": ["="],
    "GE": [">="],
    "GT": [">"],
    "LARROW": ["<-"],
    "LBRACE": ["{"],
    "LBRACKET": ["["],
    "LPAREN": ["("],
    "LT": ["<"],
    "MINUS": ["-"],
    "PLUS": ["+"],
    "QUESTION": ["?"],
    "RARROW": ["->"],
    "RBRACE": ["}"],
    "RBRACKET": ["]"],
    "RPAREN": [")"],
    "SEMICOLON": [";"],
    "SLASH": ["/"],
    "STAR": ["*"],
    "TILD": ["~"],
    "UNDERSCORE": ["_"],
}

MANUAL_REGEX_RULES: Dict[str, str] = {
    "LIDENT": "[a-z_][A-Za-z0-9_']*",
    "UIDENT": "[A-Z][A-Za-z0-9_']*",
    "TIDENT": "\"'\" [A-Za-z][A-Za-z0-9_']* | [A-Za-z][A-Za-z0-9_']*",
    "MIDENT": "[A-Za-z0-9_.]+",
    "UINT": "[0-9]+",
    "DECIMAL": "[0-9]+ \".\" [0-9]+",
    "EXPR": "[^\\r\\n]+",
    "SWAP_BODY": "([.][.]|[^.])+",
}

PATTERN_BLACKLIST = {"STRING"}

EXTRA_GRAMMAR_RULES = [
    'WS_CHAR ::= " " | "\\t" | "\\r" | "\\n"',
    "WS_OPT ::= (WS_CHAR)*",
    "EXPR_CHAR ::= [^\\r\\n]",
    "EXPR_BODY ::= EXPR_CHAR EXPR_BODY | EXPR_CHAR",
    "EXPR ::= EXPR_BODY | ε",
]

# Heads whose literal-level fallback productions collapse to bare EXPR,
# letting arbitrary text pass through without structural tokens. Dropping
# those bodies keeps the literal grammar closer to what the strict
# tokenizer enforces without requiring a huge expression expansion.
UNSTRUCTURED_FALLBACKS: Dict[str, Set[Tuple[str, ...]]] = {
    "instr": {("EXPR",)},
}

MANUAL_HEADS: Dict[str, List[Tuple[str, ...]]] = {
    # phltactic productions collapse away during expression pruning, but the
    # literal CFG still needs the SWAP anchor so lines like `swap 3 3.` don't
    # devolve entirely into EXPR. Accept either a structured iplist1 tail (if
    # present) or fall back to a single EXPR span.
    "phltactic": [
        ("SWAP", "SWAP_BODY"),
        ("SWAP", "EXPR"),
    ],
}

Grammar = Dict[str, List[Dict[str, Sequence[str]]]]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Attach literal definitions to every terminal in the reduced grammar."
    )
    parser.add_argument(
        "--grammar",
        type=Path,
        default=DEFAULT_GRAMMAR,
        help="Path to grammar_reduced_expr.json (default: %(default)s).",
    )
    parser.add_argument(
        "--lexer",
        type=Path,
        default=DEFAULT_LEXER,
        help="Path to grammar_raw.json (default: %(default)s).",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="Where to write the literal-friendly EBNF (default: %(default)s).",
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="Fail if any terminals fall back to placeholders.",
    )
    return parser.parse_args()


def load_json(path: Path) -> Dict[str, object]:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def ensure_alias(grammar: Grammar, head: str, body: Sequence[str]) -> None:
    if head in grammar:
        return
    grammar[head] = [{"body_symbols": list(body), "raw_body": "[synthetic] alias"}]


def inject_manual_heads(grammar: Grammar) -> None:
    for head, bodies in MANUAL_HEADS.items():
        if head not in grammar:
            grammar[head] = []
        for body in bodies:
            grammar[head].append({"body_symbols": list(body), "raw_body": "[synthetic] manual"})


def prune_unstructured(grammar: Grammar) -> int:
    removed = 0
    for head, forbidden in UNSTRUCTURED_FALLBACKS.items():
        productions = grammar.get(head)
        if not productions:
            continue
        kept: List[Dict[str, Sequence[str]]] = []
        for prod in productions:
            body = tuple(prod.get("body_symbols") or [])
            if body in forbidden:
                removed += 1
                continue
            kept.append(prod)
        grammar[head] = kept
    return removed


def collect_terminals(grammar: Grammar) -> Set[str]:
    nonterminals = set(grammar.keys())
    terminals: Set[str] = set()
    for productions in grammar.values():
        for prod in productions:
            for symbol in prod.get("body_symbols") or []:
                if not symbol:
                    continue
                if symbol == "ε":
                    continue
                if symbol in nonterminals:
                    continue
                terminals.add(symbol)
    return terminals


def escape_literal(text: str) -> str:
    return text.replace("\\", "\\\\").replace('"', '\\"')


def format_literal(text: str) -> str:
    return f"\"{escape_literal(text)}\""


def sanitize_pattern(pattern: str) -> str:
    """
    Menhir stores OCaml regexes; strip ^/$ anchors (if any) so the expression
    can plug directly into the EBNF RHS.
    """

    cleaned = pattern
    if cleaned.startswith("^"):
        cleaned = cleaned[1:]
    if cleaned.endswith("$"):
        cleaned = cleaned[:-1]
    return cleaned.strip()


def build_token_rules(
    lexer_meta: Dict[str, Dict[str, object]],
    terminals: Set[str],
) -> Dict[str, str]:
    token_rules: Dict[str, str] = {}

    for name, spec in lexer_meta.items():
        literals = spec.get("literals") or []
        pattern = spec.get("pattern")
        if literals:
            literal_alts = sorted({str(lit) for lit in literals if lit})
            token_rules[name] = " | ".join(format_literal(lit) for lit in literal_alts)
        elif pattern:
            token_rules[name] = sanitize_pattern(str(pattern))

    for name, literals in PUNCTUATION_OVERRIDES.items():
        literal_expr = " | ".join(format_literal(lit) for lit in literals)
        token_rules.setdefault(name, literal_expr)

    for name, regex in MANUAL_REGEX_RULES.items():
        token_rules[name] = regex

    for name in PATTERN_BLACKLIST:
        token_rules.pop(name, None)

    # Only keep rules for terminals we actually reference
    filtered = {name: rhs for name, rhs in token_rules.items() if name in terminals}
    return filtered


def placeholder_for(token: str) -> str:
    return f"__{token.lower()}__"


def decorate_body_symbols(body: Sequence[str]) -> str:
    if not body:
        return "ε"
    decorated: List[str] = ["WS_OPT"]
    for symbol in body:
        decorated.append(symbol)
        decorated.append("WS_OPT")
    return " ".join(decorated)


def write_ebnf(
    grammar: Grammar,
    terminals: Iterable[str],
    token_rules: Dict[str, str],
    placeholders: Dict[str, str],
    output_path: Path,
) -> None:
    heads = sorted(grammar.keys())
    lines: List[str] = []
    for head in heads:
        bodies: List[str] = []
        for prod in grammar[head]:
            symbols = prod.get("body_symbols") or []
            bodies.append(decorate_body_symbols(symbols))
        rhs = " | ".join(bodies) if bodies else "ε"
        lines.append(f"{head} ::= {rhs}")
    lines.append("")
    for token in sorted(terminals):
        if token in {"ε", ""}:
            continue
        rhs = token_rules.get(token)
        if not rhs:
            continue
        lines.append(f"{token} ::= {rhs}")
    lines.append("")
    lines.extend(EXTRA_GRAMMAR_RULES)

    note_lines = []
    if placeholders:
        items = ", ".join(f"{name}->{placeholder}" for name, placeholder in sorted(placeholders.items()))
        note_lines.append(f"# Placeholders emitted for: {items}")
    if note_lines:
        lines.append("")
        lines.extend(note_lines)
    output_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    args = parse_args()
    grammar = load_json(args.grammar)
    ensure_alias(grammar, "X", ["EXPR"])
    inject_manual_heads(grammar)
    removed = prune_unstructured(grammar)

    lexer_meta = load_json(args.lexer).get("lexer", {})

    terminals = collect_terminals(grammar)
    for synthetic in {"EXPR", "EXPR_BODY", "EXPR_CHAR", "WS_OPT"}:
        terminals.discard(synthetic)
    placeholders: Dict[str, str] = {}

    token_rules = build_token_rules(lexer_meta, terminals)
    for token in sorted(terminals):
        if token in token_rules:
            continue
        placeholder = placeholder_for(token)
        token_rules[token] = format_literal(placeholder)
        placeholders[token] = placeholder

    if args.strict and placeholders:
        missing = ", ".join(sorted(placeholders.keys()))
        print(
            f"Cannot emit literal grammar: missing literal definitions for {len(placeholders)} tokens: {missing}",
            file=sys.stderr,
        )
        sys.exit(1)

    write_ebnf(grammar, terminals, token_rules, placeholders, args.output)
    print(f"Wrote literal-friendly EBNF to {args.output}")
    if removed:
        print(f"Pruned {removed} unstructured fallback production(s) before emission.")
    if placeholders:
        print(
            f"Warning: {len(placeholders)} tokens used placeholders "
            f"(rerun with --strict to block this): {', '.join(sorted(placeholders))}",
            file=sys.stderr,
        )


if __name__ == "__main__":
    main()

