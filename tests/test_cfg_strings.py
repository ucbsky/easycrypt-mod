#!/usr/bin/env python3
"""
Sanity-check the literal-friendly EBNF by parsing raw EasyCrypt lines using
`transformers-cfg`'s `StringRecognizer`. This mimics the grammar automaton that
`IncrementalGrammarConstraint` builds, but keeps the test lightweight by
avoiding the HF tokenizer/torch stack.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path
from typing import Iterable, List, Sequence, Tuple

from transformers import AutoTokenizer  # type: ignore[import]
from transformers_cfg.grammar_utils import IncrementalGrammarConstraint  # type: ignore[import]

PROJECT_ROOT = Path(__file__).resolve().parents[1]
OUT_DIR = PROJECT_ROOT / "out"

GOOD_CASE = PROJECT_ROOT / "grammar_examples" / "good.ec"
BAD_CASE = PROJECT_ROOT / "grammar_examples" / "bad.ec"
LITERAL_EBNF = OUT_DIR / "grammar_reduced_expr_literals.ebnf"


def ensure_artifacts(skip_refresh: bool) -> None:
    if skip_refresh:
        return
    subprocess.run(
        [sys.executable, str(OUT_DIR / "inspect_raw_grammar.py")],
        check=True,
    )
    subprocess.run(
        [sys.executable, str(OUT_DIR / "emit_literal_grammar.py")],
        check=True,
    )


def load_constraint() -> Tuple[IncrementalGrammarConstraint, AutoTokenizer]:
    grammar_str = LITERAL_EBNF.read_text(encoding="utf-8")
    tokenizer = AutoTokenizer.from_pretrained("gpt2")
    constraint = IncrementalGrammarConstraint(
        grammar_str=grammar_str,
        start_rule_name="Line",
        tokenizer=tokenizer,
    )
    return constraint, tokenizer


def iter_lines(path: Path) -> Iterable[Tuple[int, str]]:
    for idx, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not raw.strip():
            continue
        if raw.lstrip().startswith("#"):
            continue
        yield idx, raw.rstrip("\n")


def evaluate(
    constraint: IncrementalGrammarConstraint,
    lines: Sequence[Tuple[int, str]],
    expect_success: bool,
) -> Tuple[bool, List[int]]:
    offending: List[int] = []
    for lineno, text in lines:
        state = constraint.string_recognizer.get_initial_parsing_state()
        try:
            accepted = constraint.string_recognizer._accept_string(text, state)
        except RecursionError:
            accepted = False
        if expect_success and not accepted:
            offending.append(lineno)
        if not expect_success and accepted:
            offending.append(lineno)
    return len(offending) == 0, offending


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Validate literal-level EasyCrypt grammar with transformers-cfg's recognizer."
    )
    parser.add_argument(
        "--skip-refresh",
        action="store_true",
        help="Assume grammar artifacts are up to date.",
    )
    args = parser.parse_args()

    ensure_artifacts(args.skip_refresh)
    constraint, tokenizer = load_constraint()

    scenarios = [
        ("good", GOOD_CASE, True),
        ("bad", BAD_CASE, False),
    ]
    overall_ok = True

    for label, path, expect_success in scenarios:
        lines = list(iter_lines(path))
        ok, offending = evaluate(constraint, lines, expect_success)
        overall_ok &= ok
        status = "PASS" if ok else "FAIL"
        print(f"[{status}] {label}: {path}")
        if offending:
            tag = (
                "wrongfully-rejected line numbers"
                if expect_success
                else "unexpectedly-parsing line numbers"
            )
            print(f"    {tag}: {offending}")

    if not overall_ok:
        sys.exit(1)


if __name__ == "__main__":
    main()

