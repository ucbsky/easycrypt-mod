#!/usr/bin/env python3
"""
Smoke-test the minimalist EasyCrypt grammar directly against the reference line
corpora. The goal is not perfect coverage but a fast signal that the simplified
CFG still aligns with most curated examples while filtering out the noisier
`bad.ec` snippets.
"""

from __future__ import annotations

import argparse
import math
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

from transformers import AutoTokenizer  # type: ignore[import]
from transformers_cfg.grammar_utils import IncrementalGrammarConstraint  # type: ignore[import]

import importlib.util

PROJECT_ROOT = Path(__file__).resolve().parents[1]
GOOD_CASE = PROJECT_ROOT / "grammar_examples" / "good_simple.ec"
BAD_CASE = PROJECT_ROOT / "grammar_examples" / "bad.ec"
PARSE_EC_PATH = PROJECT_ROOT / "parse_easycrypt.py"

GRAMMAR_VARIANTS: Dict[str, Dict[str, float]] = {
    "strict": {"good_fraction": 0.20, "bad_fraction": 0.30},
    "lenient": {"good_fraction": 0.0, "bad_fraction": 0.50},
}


def load_grammar_text(variant: str) -> str:
    module_path = PROJECT_ROOT / "out" / "emit_minimal_grammar.py"
    spec = importlib.util.spec_from_file_location("emit_minimal_grammar", module_path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Cannot load grammar module from {module_path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)  # type: ignore[assignment]
    if variant == "lenient":
        build_fn = getattr(module, "build_lenient_ebnf", None)
    else:
        build_fn = getattr(module, "build_minimal_ebnf", None)
    if not callable(build_fn):
        raise RuntimeError(f"Grammar module is missing builder for variant '{variant}'")
    return build_fn()


def load_constraint(variant: str) -> IncrementalGrammarConstraint:
    grammar_str = load_grammar_text(variant)
    tokenizer = AutoTokenizer.from_pretrained("gpt2")
    return IncrementalGrammarConstraint(
        grammar_str=grammar_str,
        start_rule_name="Line",
        tokenizer=tokenizer,
    )


def iter_lines(path: Path) -> Iterable[Tuple[str, str]]:
    for idx, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        stripped = raw.rstrip("\n")
        if not stripped.strip():
            continue
        if stripped.lstrip().startswith("#"):
            continue
        yield str(idx), stripped


def evaluate(
    constraint: IncrementalGrammarConstraint,
    lines: Sequence[Tuple[str, str]],
) -> Tuple[List[str], List[str]]:
    accepted: List[str] = []
    rejected: List[str] = []
    for line_id, text in lines:
        state = constraint.string_recognizer.get_initial_parsing_state()
        try:
            ok = constraint.string_recognizer._accept_string(text, state)
        except RecursionError:
            ok = False
        (accepted if ok else rejected).append(line_id)
    return accepted, rejected


def summarize(
    prefix: str,
    accepted: List[str],
    rejected: List[str],
    *,
    max_rejections: int | None = None,
) -> None:
    print(f"[{prefix}] accepted={len(accepted)} rejected={len(rejected)}")
    if rejected:
        display = rejected
        extra = 0
        if max_rejections is not None and len(rejected) > max_rejections:
            display = rejected[:max_rejections]
            extra = len(rejected) - max_rejections
        print(f"    rejected lines: {display}")
        if extra:
            print(f"    ... {extra} more")


def rate(numerator: int, denominator: int) -> float:
    if denominator == 0:
        return 0.0
    return (numerator / denominator) * 100.0


def percentage_cap(total: int, fraction: float) -> int:
    if total <= 0:
        return 0
    return max(0, math.ceil(total * fraction))


def load_parse_module(script_path: Path):
    spec = importlib.util.spec_from_file_location("parse_easycrypt", script_path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Cannot import parser from {script_path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)  # type: ignore[assignment]
    if not hasattr(module, "parse_easycrypt_file"):
        raise RuntimeError("parse_easycrypt.py is missing parse_easycrypt_file()")
    return module


def list_ec_files(path: Path) -> List[Path]:
    if path.is_file():
        return [path]
    if not path.exists():
        raise FileNotFoundError(f"{path} does not exist")
    return sorted(p for p in path.rglob("*.ec") if p.is_file())


def extract_proof_lines(
    ec_path: Path,
    parser_module,
) -> List[Tuple[int, str]]:
    parsed = parser_module.parse_easycrypt_file(ec_path)
    lines: List[Tuple[int, str]] = []
    for item in parsed.get("content", []):
        if item.get("type") != "lemma":
            continue
        proof_text = item.get("proof") or ""
        body_lines: List[str] = []
        for raw in proof_text.splitlines():
            stripped = raw.strip()
            if not stripped:
                continue
            lowered = stripped.lower()
            if lowered in {"proof.", "qed."}:
                continue
            body_lines.append(stripped)
        for idx, text in enumerate(body_lines, 1):
            identifier = f"{ec_path}:{item.get('name','?')}:{idx}"
            lines.append((identifier, text))
    return lines


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Check the minimalist EasyCrypt grammar against example corpora."
    )
    parser.add_argument("--good", type=Path, default=GOOD_CASE, help="Path to good samples.")
    parser.add_argument("--bad", type=Path, default=BAD_CASE, help="Path to negative samples.")
    parser.add_argument(
        "--max-good-fail",
        type=int,
        default=None,
        help="Override the allowed number of rejected good lines (default: 20%% of total).",
    )
    parser.add_argument(
        "--max-bad-pass",
        type=int,
        default=None,
        help="Override the allowed number of accepted bad lines (default: 30%% of total).",
    )
    parser.add_argument(
        "--proof-path",
        type=Path,
        help="File or directory of .ec files whose lemma proof lines should be evaluated.",
    )
    parser.add_argument(
        "--parse-script",
        type=Path,
        default=PARSE_EC_PATH,
        help="Path to parse_easycrypt.py (default: %(default)s).",
    )
    args = parser.parse_args()

    good_lines = list(iter_lines(args.good))
    bad_lines = list(iter_lines(args.bad))
    proof_lines: List[Tuple[str, str]] = []
    if args.proof_path:
        parser_module = load_parse_module(args.parse_script)
        ec_files = list_ec_files(args.proof_path)
        for ec_file in ec_files:
            proof_lines.extend(extract_proof_lines(ec_file, parser_module))
        print(
            f"Collected {len(proof_lines)} proof lines from {len(ec_files)} file(s) under {args.proof_path}"
        )

    failures: List[str] = []

    for variant, cfg in GRAMMAR_VARIANTS.items():
        print(f"\n=== {variant.upper()} grammar ===")
        constraint = load_constraint(variant)

        good_ok, good_fail = evaluate(constraint, good_lines)
        summarize(f"{variant}:good", good_ok, good_fail)

        bad_ok, bad_fail = evaluate(constraint, bad_lines)
        summarize(f"{variant}:bad", bad_ok, bad_fail)

        print(
            f"[{variant} stats] good success={rate(len(good_ok), len(good_lines)):.1f}% "
            f"(accepted {len(good_ok)}/{len(good_lines)})"
        )
        print(
            f"[{variant} stats] bad success={rate(len(bad_fail), len(bad_lines)):.1f}% "
            f"(rejected {len(bad_fail)}/{len(bad_lines)})"
        )

        good_cap = args.max_good_fail
        if good_cap is None:
            good_cap = percentage_cap(len(good_lines), cfg["good_fraction"])
            good_label = (
                f"{int(cfg['good_fraction']*100)}% of {len(good_lines)}"
                if cfg["good_fraction"] > 0
                else "no rejections allowed"
            )
        else:
            good_label = f"override {good_cap}"

        bad_cap = args.max_bad_pass
        if bad_cap is None:
            bad_cap = percentage_cap(len(bad_lines), cfg["bad_fraction"])
            bad_label = (
                f"{int(cfg['bad_fraction']*100)}% of {len(bad_lines)}"
                if cfg["bad_fraction"] < 1
                else "no cap"
            )
        else:
            bad_label = f"override {bad_cap}"

        if len(good_fail) > good_cap:
            failures.append(
                f"[{variant}] Too many good lines rejected: {len(good_fail)} > {good_cap} ({good_label})"
            )
        if len(bad_ok) > bad_cap:
            failures.append(
                f"[{variant}] Too many bad lines accepted: {len(bad_ok)} > {bad_cap} ({bad_label})"
            )

        if proof_lines:
            proof_ok, proof_fail = evaluate(constraint, proof_lines)
            summarize(
                f"{variant}:proof",
                proof_ok,
                proof_fail,
                max_rejections=10,
            )
            print(
                f"[{variant} proof stats] success={rate(len(proof_ok), len(proof_lines)):.1f}% "
                f"(accepted {len(proof_ok)}/{len(proof_lines)})"
            )

    if failures:
        print("\nValidation failures:")
        for msg in failures:
            print(f"  - {msg}")
        raise SystemExit(1)


if __name__ == "__main__":
    main()

