#!/usr/bin/env python3
"""
Smoke-test the minimalist EasyCrypt grammar directly against the reference line
corpora. The goal is not perfect coverage but a fast signal that the simplified
CFG still aligns with most curated examples while filtering out the noisier
`bad.ec` snippets.
"""

from __future__ import annotations

import argparse
from pathlib import Path
from typing import Iterable, List, Sequence, Tuple

from transformers import AutoTokenizer  # type: ignore[import]
from transformers_cfg.grammar_utils import IncrementalGrammarConstraint  # type: ignore[import]

import importlib.util

PROJECT_ROOT = Path(__file__).resolve().parents[1]
GOOD_CASE = PROJECT_ROOT / "grammar_examples" / "good_simple.ec"
BAD_CASE = PROJECT_ROOT / "grammar_examples" / "bad.ec"


def load_grammar_text() -> str:
    module_path = PROJECT_ROOT / "out" / "emit_minimal_grammar.py"
    spec = importlib.util.spec_from_file_location("emit_minimal_grammar", module_path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Cannot load grammar module from {module_path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)  # type: ignore[assignment]
    build_fn = getattr(module, "build_minimal_ebnf", None)
    if not callable(build_fn):
        raise RuntimeError("Grammar module is missing build_minimal_ebnf()")
    return build_fn()


def load_constraint() -> IncrementalGrammarConstraint:
    grammar_str = load_grammar_text()
    tokenizer = AutoTokenizer.from_pretrained("gpt2")
    return IncrementalGrammarConstraint(
        grammar_str=grammar_str,
        start_rule_name="Line",
        tokenizer=tokenizer,
    )


def iter_lines(path: Path) -> Iterable[Tuple[int, str]]:
    for idx, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        stripped = raw.rstrip("\n")
        if not stripped.strip():
            continue
        if stripped.lstrip().startswith("#"):
            continue
        yield idx, stripped


def evaluate(
    constraint: IncrementalGrammarConstraint,
    lines: Sequence[Tuple[int, str]],
) -> Tuple[List[int], List[int]]:
    accepted: List[int] = []
    rejected: List[int] = []
    for lineno, text in lines:
        state = constraint.string_recognizer.get_initial_parsing_state()
        try:
            ok = constraint.string_recognizer._accept_string(text, state)
        except RecursionError:
            ok = False
        (accepted if ok else rejected).append(lineno)
    return accepted, rejected


def summarize(prefix: str, accepted: List[int], rejected: List[int]) -> None:
    print(f"[{prefix}] accepted={len(accepted)} rejected={len(rejected)}")
    if rejected:
        print(f"    rejected lines: {rejected}")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Check the minimalist EasyCrypt grammar against example corpora."
    )
    parser.add_argument("--good", type=Path, default=GOOD_CASE, help="Path to good samples.")
    parser.add_argument("--bad", type=Path, default=BAD_CASE, help="Path to negative samples.")
    parser.add_argument(
        "--max-good-fail",
        type=int,
        default=6,
        help="Allow up to this many good lines to be rejected.",
    )
    parser.add_argument(
        "--max-bad-pass",
        type=int,
        default=3,
        help="Allow up to this many bad lines to be accepted.",
    )
    args = parser.parse_args()

    constraint = load_constraint()

    good_lines = list(iter_lines(args.good))
    good_ok, good_fail = evaluate(constraint, good_lines)
    summarize("good", good_ok, good_fail)
    if len(good_fail) > args.max_good_fail:
        raise SystemExit(
            f"Too many good lines rejected: {len(good_fail)} > {args.max_good_fail}"
        )

    bad_lines = list(iter_lines(args.bad))
    bad_ok, bad_fail = evaluate(constraint, bad_lines)
    summarize("bad", bad_ok, bad_fail)
    if len(bad_ok) > args.max_bad_pass:
        raise SystemExit(
            f"Too many bad lines accepted: {len(bad_ok)} > {args.max_bad_pass}"
        )


if __name__ == "__main__":
    main()

