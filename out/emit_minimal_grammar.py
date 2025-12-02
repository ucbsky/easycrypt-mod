#!/usr/bin/env python3
"""
Emit a deliberately tiny EasyCrypt grammar aimed at quick debugging loops.

The grammar keeps fewer than 25 productions by modeling each input line as a
keyword-driven clause that optionally carries a free-form payload. The payload
is intentionally opaque (it just bans newlines, statement terminators, and
semicolon separators) so that the grammar stays concise while still accepting
most structural lines in `good_simple.ec` and rejecting the majority of the
free-form snippets in `bad.ec`.
"""

from __future__ import annotations

import argparse
from pathlib import Path
from textwrap import dedent

DEFAULT_OUTPUT = Path("out/minimal_easycrypt.ebnf")

MINIMAL_EBNF = dedent(
    """
    Line ::= WS_OPT ClauseChain WS_OPT "." | WS_OPT Prefix WS_OPT ClauseChain WS_OPT "."
    ClauseChain ::= Clause | Clause ";" WS_OPT ClauseChain
    Prefix ::= BULLET WS_OPT
    BULLET ::= "+" | "-" | "*"
    Clause ::= KeywordBare | KeywordBare Tail | KeywordStar | KeywordStar Tail | KeywordTailOnly Tail
    Tail ::= Separator WS_OPT TailStart | Separator WS_OPT TailStart TailRest | LPAREN WS_OPT TailAfterParen
    Separator ::= WS_PLUS | ARROW
    ARROW ::= "=>"
    TailStart ::= START_CHAR | LPAREN TailAfterParen
    TailRest ::= TailChar TailRest | TailChar
    TailChar ::= SAFE_CHAR | LPAREN TailAfterParen
    TailAfterParen ::= LPAREN TailAfterParen | NONLPAREN_CHAR | NONLPAREN_CHAR TailRest
    LPAREN ::= "("
    START_CHAR ::= [^(:.;\\r\\n]
    SAFE_CHAR ::= [^(.;\\r\\n]
    NONLPAREN_CHAR ::= [^(*.;\\r\\n]
    WS_PLUS ::= WS_CHAR WS_OPT
    WS_OPT ::= (WS_CHAR)*
    WS_CHAR ::= " " | "\\t"
    KeywordBare ::= "proof" | "qed" | "have" | "proc" | "call" | "rnd" | "skip" | "rewrite" | "trivial" | "field" | "smt" | "move" | "inline" | "sim" | "auto" | "apply" | "while" | "swap" | "wp" | "byphoare" | "byequiv" | "do" | "progress" | "split" | "done" | "case" | "simplify" | "elim"
    KeywordStar ::= "proc*" | "inline*"
    KeywordTailOnly ::= "by"
    """
).strip()


def build_minimal_ebnf() -> str:
    """Return the minimalist EasyCrypt grammar."""
    return MINIMAL_EBNF + "\n"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Write a minimalist EasyCrypt grammar for quick CFG experiments."
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="Destination EBNF path (default: %(default)s). Pass '-' for stdout.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    grammar = build_minimal_ebnf()
    if str(args.output) == "-":
        print(grammar, end="")
        return
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(grammar, encoding="utf-8")
    print(f"Wrote minimalist EasyCrypt grammar to {args.output}")


if __name__ == "__main__":
    main()

