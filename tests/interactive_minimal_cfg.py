#!/usr/bin/env python3
"""
Interactive playground for the minimalist EasyCrypt grammar.

The script instantiates the same `IncrementalGrammarConstraint` used in the
regression tests and lets you explore the valid GPT-2 tokens one step at a time.
At each prompt it prints every currently accepted token (ID, raw token string,
and decoded text). You can then enter the token you want to feed—either by ID,
by exact token string (e.g. `Ġproof`), or by literal text that happens to map to
exactly one GPT-2 token. The session keeps track of the accumulated text and can
be reset at any point.

Commands:
  :help        Show instructions
  :list        Re-print the currently accepted tokens
  :reset       Reset the parsing state to the beginning of the line
  :batch TEXT  Feed arbitrary text (tokenized via the current tokenizer)
  :quit        Exit the session (`:q` works too)
"""

from __future__ import annotations

import argparse
import importlib.util
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, List, Sequence, Tuple

import torch
from transformers import AutoTokenizer  # type: ignore[import]
from transformers_cfg.grammar_utils import IncrementalGrammarConstraint  # type: ignore[import]

PROJECT_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_EMITTER = PROJECT_ROOT / "out" / "emit_minimal_grammar.py"
DEFAULT_TOKENIZER = "gpt2"


@dataclass
class TokenChoice:
    token_id: int
    vocab_token: str
    decoded: str


def load_minimal_grammar(module_path: Path) -> str:
    spec = importlib.util.spec_from_file_location("emit_minimal_grammar", module_path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Cannot import emitter from {module_path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)  # type: ignore[arg-type]
    builder = getattr(module, "build_minimal_ebnf", None)
    if not callable(builder):
        raise RuntimeError("Emitter module is missing build_minimal_ebnf()")
    return builder()


def build_constraint(grammar: str, tokenizer_name: str, start_rule: str) -> Tuple[IncrementalGrammarConstraint, AutoTokenizer]:
    tokenizer = AutoTokenizer.from_pretrained(tokenizer_name)
    constraint = IncrementalGrammarConstraint(
        grammar_str=grammar,
        start_rule_name=start_rule,
        tokenizer=tokenizer,
    )
    return constraint, tokenizer


def collect_allowed_tokens(
    constraint: IncrementalGrammarConstraint,
    tokenizer: AutoTokenizer,
    state,
) -> List[TokenChoice]:
    if not getattr(state, "stacks", None):
        return []
    acceptance = constraint.get_next_token_acceptance(state, torch.device("cpu"))
    token_ids = torch.nonzero(acceptance, as_tuple=False).view(-1).tolist()
    choices: List[TokenChoice] = []
    for token_id in token_ids:
        vocab_tok = tokenizer.convert_ids_to_tokens(token_id)
        decoded = tokenizer.decode([token_id])
        choices.append(TokenChoice(token_id=token_id, vocab_token=vocab_tok, decoded=decoded))
    choices.sort(key=lambda choice: choice.token_id)
    return choices


def resolve_token_id(user_input: str, tokenizer: AutoTokenizer) -> int:
    raw = user_input.strip()
    if raw.startswith("id:"):
        return int(raw.split(":", 1)[1], 10)
    vocab_id = tokenizer.convert_tokens_to_ids(raw)
    vocab_token = tokenizer.convert_ids_to_tokens(vocab_id)
    if vocab_token == raw:
        return vocab_id
    encoded = tokenizer.encode(raw, add_special_tokens=False)
    if len(encoded) != 1:
        raise ValueError(
            f"Input {raw!r} does not map to a single token (produced {len(encoded)} ids)"
        )
    return encoded[0]


def print_allowed(choices: Sequence[TokenChoice], limit: int) -> None:
    if not choices:
        print("\n(Grammar is in a terminal state; use :reset to start a new line.)\n")
        return
    print(f"\nAllowed next tokens ({len(choices)} total):")
    head = choices[:limit]
    for choice in head:
        decoded = choice.decoded.replace("\n", "\\n")
        print(f"  id={choice.token_id:>5}  vocab={choice.vocab_token!r:<15} decoded={decoded!r}")
    if len(choices) > limit:
        print(f"  ... {len(choices) - limit} more token(s) omitted (use --limit to adjust)")
    print()


def format_history(tokenizer: AutoTokenizer, accepted_ids: Sequence[int]) -> str:
    if not accepted_ids:
        return ""
    return tokenizer.decode(accepted_ids)


def try_feed_token(
    token_id: int,
    constraint: IncrementalGrammarConstraint,
    tokenizer: AutoTokenizer,
    state: Any,
    accepted_ids: List[int],
    allowed: List[TokenChoice],
    limit: int,
    show_allowed: bool = True,
) -> Tuple[Any, List[TokenChoice], bool]:
    allowed_ids = {choice.token_id for choice in allowed}
    if token_id not in allowed_ids:
        token_repr = tokenizer.convert_ids_to_tokens(token_id)
        print(f"Token id={token_id} ({token_repr!r}) is not currently accepted.")
        return state, allowed, False
    try:
        state = constraint._update_state_with_token_id(token_id, state)  # type: ignore[attr-defined]
    except ValueError as exc:
        print(f"Grammar rejected the token: {exc}")
        return state, allowed, False
    accepted_ids.append(token_id)
    history = format_history(tokenizer, accepted_ids)
    vocab_tok = tokenizer.convert_ids_to_tokens(token_id)
    print(f"Accepted id={token_id} ({vocab_tok!r}). Current text: {history!r}")
    allowed = collect_allowed_tokens(constraint, tokenizer, state)
    if show_allowed:
        print_allowed(allowed, limit)
    return state, allowed, True


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Interactively explore the minimalist EasyCrypt grammar using transformers-cfg."
    )
    parser.add_argument(
        "--emitter",
        type=Path,
        default=DEFAULT_EMITTER,
        help="Path to emit_minimal_grammar.py (default: %(default)s).",
    )
    parser.add_argument(
        "--start-rule",
        type=str,
        default="Line",
        help="EBNF start rule to feed into transformers-cfg.",
    )
    parser.add_argument(
        "--tokenizer",
        type=str,
        default=DEFAULT_TOKENIZER,
        help="HF tokenizer name (default: %(default)s).",
    )
    parser.add_argument(
        "--limit",
        type=int,
        default=40,
        help="Maximum number of allowed tokens to display per step.",
    )
    args = parser.parse_args()

    grammar = load_minimal_grammar(args.emitter)
    constraint, tokenizer = build_constraint(grammar, args.tokenizer, args.start_rule)
    state = constraint.string_recognizer.get_initial_parsing_state()
    accepted_ids: List[int] = []

    print("Interactive minimal CFG explorer.")
    print("Commands: :help, :list, :reset, :batch, :quit")
    print("Token input formats:")
    print("  * Exact vocab token (e.g., Ġproof)")
    print("  * Raw text that encodes to a single token (e.g., proof)")
    print("  * Explicit id via id:1234")

    allowed = collect_allowed_tokens(constraint, tokenizer, state)
    print_allowed(allowed, args.limit)

    while True:
        try:
            user_input = input("token> ").strip()
        except EOFError:
            print()
            break
        except KeyboardInterrupt:
            print("\nInterrupted.")
            break
        if not user_input:
            continue
        lowered = user_input.lower()
        if lowered in {":q", ":quit"}:
            break
        if lowered in {":help", "help"}:
            print(__doc__)
            continue
        if lowered in {":list", ":l"}:
            allowed = collect_allowed_tokens(constraint, tokenizer, state)
            print_allowed(allowed, args.limit)
            continue
        if lowered.startswith(":batch"):
            payload = user_input[len(":batch") :].strip()
            if not payload:
                print("Usage: :batch <arbitrary text>")
                continue
            token_ids = tokenizer.encode(payload, add_special_tokens=False)
            if not token_ids:
                print("Batch payload produced no tokens.")
                continue
            print(f"Batch feeding {len(token_ids)} token(s) derived from {payload!r}")
            for idx, token_id in enumerate(token_ids):
                state, allowed, ok = try_feed_token(
                    token_id,
                    constraint,
                    tokenizer,
                    state,
                    accepted_ids,
                    allowed,
                    args.limit,
                    show_allowed=idx == len(token_ids) - 1,
                )
                if not ok:
                    break
            continue
        if lowered in {":reset", ":r"}:
            state = constraint.string_recognizer.get_initial_parsing_state()
            accepted_ids.clear()
            print("State reset.")
            allowed = collect_allowed_tokens(constraint, tokenizer, state)
            print_allowed(allowed, args.limit)
            continue

        try:
            token_id = resolve_token_id(user_input, tokenizer)
        except Exception as exc:  # noqa: BLE001
            print(f"Could not interpret input as a token: {exc}")
            continue

        state, allowed, _ = try_feed_token(
            token_id,
            constraint,
            tokenizer,
            state,
            accepted_ids,
            allowed,
            args.limit,
            show_allowed=True,
        )


if __name__ == "__main__":
    try:
        main()
    except Exception as err:  # noqa: BLE001
        print(f"interactive session failed: {err}", file=sys.stderr)
        raise

