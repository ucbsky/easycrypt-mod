#!/usr/bin/env python3
"""
Rewrite EasyCrypt lemma proofs by replaying tactics extracted from an AST JSON.

Given an EasyCrypt source file and its proof AST (as produced by EasyCrypt's
`--proofast` output), this script traverses each lemma's tactic graph goal by
goal, emits a depth-first ordering where each tactic is applied to a single
goal, and replaces the original proof block with that reconstructed script.

Usage:
    ./formatter path/to/file.ec path/to/file.proofast.json [--lemmas L1 L2]
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import parse_easycrypt


@dataclass
class TacticOccurrence:
    """Represents applying a tactic to a specific goal."""

    idx: int
    goal: int
    text: str | None
    outputs: List[int]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Format EasyCrypt proofs via AST replays.")
    parser.add_argument("easycrypt_file", help="Path to the EasyCrypt source (.ec)")
    parser.add_argument("ast_file", help="Path to the proof AST JSON")
    parser.add_argument(
        "--lemmas",
        nargs="+",
        metavar="LEMMA",
        help="Optional subset of lemma names to format (defaults to all from AST)",
    )
    parser.add_argument(
        "--dump-graph",
        default="goal-graph.json",
        help="If set, write the DFS goal graph per lemma as JSON to PATH",
    )
    return parser.parse_args()


def load_ast(path: Path) -> Tuple[Dict[str, dict], List[str]]:
    try:
        data = json.loads(path.read_text())
    except OSError as err:
        raise SystemExit(f"Failed to read AST file {path}: {err}") from err
    except json.JSONDecodeError as err:
        raise SystemExit(f"AST file {path} is not valid JSON: {err}") from err

    lemmas = {}
    order: List[str] = []
    for lemma in data.get("lemmas", []):
        name = lemma.get("name")
        if not name:
            continue
        lemmas[name] = lemma
        order.append(name)
    return lemmas, order


def assign_outputs(inputs: Sequence[int], outputs: Sequence[int]) -> List[Tuple[int, List[int]]]:
    """Distribute produced goals among input goals."""
    if not inputs:
        return []
    if len(inputs) == 1:
        return [(inputs[0], list(outputs))]

    if not outputs:
        return [(goal, []) for goal in inputs]

    if outputs and len(outputs) % len(inputs) == 0:
        chunk = len(outputs) // len(inputs)
        distributed: List[Tuple[int, List[int]]] = []
        cursor = 0
        for goal in inputs:
            distributed.append((goal, list(outputs[cursor : cursor + chunk])))
            cursor += chunk
        return distributed

    distributed = [(inputs[0], list(outputs))]
    distributed.extend((goal, []) for goal in inputs[1:])
    return distributed


def _format_payload(payload: object) -> str:
    try:
        return json.dumps(payload, indent=2, sort_keys=True)
    except TypeError:
        return repr(payload)


def _prewrite_error(reason: str, payload: object) -> None:
    formatted = _format_payload(payload)
    raise SystemExit(f"[formatter] Unsupported Prewrite: {reason}\nPayload: {formatted}")


def _apply_target_suffix(text: str, target: object) -> str:
    if not isinstance(target, str):
        return text
    suffix = target.strip()
    if not suffix:
        return text
    if text.endswith("."):
        return f"{text[:-1]} in {suffix}."
    return f"{text} in {suffix}"


def _occurs_prefix(occurs: object) -> str:
    if not isinstance(occurs, dict):
        return ""
    kind = occurs.get("kind")
    indexes = occurs.get("indexes") or []
    if not isinstance(indexes, list):
        indexes = []
    idx_text = " ".join(str(idx) for idx in indexes if idx is not None)
    if kind == "inclusive":
        return f"{{{idx_text}}}" if idx_text else "{}"
    if kind == "exclusive":
        return f"{{-{idx_text}}}" if idx_text else "{-}"
    if kind == "all":
        return "{all}"
    return ""


def _term_to_string(term: object) -> str:
    if not isinstance(term, dict):
        return ""
    head = term.get("head") or {}
    name = head.get("name")
    if not isinstance(name, str):
        return ""
    args = term.get("args") or []
    arg_texts: List[str] = []
    for arg in args:
        text = ""
        if isinstance(arg, dict):
            text = arg.get("source") or ""
            if not text:
                formula = arg.get("formula") or {}
                text = formula.get("source") or ""
        text = str(text).strip()
        if text:
            arg_texts.append(text)
    if arg_texts:
        return f"{name} {' '.join(arg_texts)}"
    return name


def _token_from_entry(src: str, global_is_rtl: bool, entry: dict, occurs: object) -> str:
    token = (src or "").strip()
    entry_side = entry.get("side") if isinstance(entry, dict) else None
    entry_is_rtl = entry_side == "r-to-l"
    final_is_rtl = global_is_rtl ^ bool(entry_is_rtl)
    if token:
        prefix = _occurs_prefix(occurs)
        if prefix and not token.startswith(prefix):
            token = f"{prefix}{token}"
        if final_is_rtl and not token.startswith("-"):
            token = f"-{token}"
        return token

    term = entry.get("term") if isinstance(entry, dict) else None
    lemma = _term_to_string(term)
    if not lemma:
        _prewrite_error("unable to reconstruct rewrite token", entry)
    prefix = _occurs_prefix(occurs)
    if prefix:
        lemma = f"{prefix}({lemma})"
    if final_is_rtl and not lemma.startswith("-"):
        lemma = f"-{lemma}"
    return lemma


def _collect_prewrite_lines(core: dict) -> List[Tuple[str, dict]]:
    args = core.get("args")
    if not isinstance(args, dict):
        _prewrite_error("missing or invalid 'args' payload", args)

    tactic_info = args.get("tactic")
    if not isinstance(tactic_info, dict) or tactic_info.get("kind") != "Prewrite":
        _prewrite_error("internal error: _render_prewrite_tactic on non-Prewrite node", tactic_info)

    raw_args = tactic_info.get("args") or []
    if not isinstance(raw_args, list) or not raw_args:
        _prewrite_error("empty or malformed 'args'", raw_args)
    target_symbol = tactic_info.get("symbol")

    lines: List[Tuple[str, dict]] = []

    for raw in raw_args:
        if not isinstance(raw, dict):
            _prewrite_error("argument entry is not an object", raw)
        argument = raw.get("argument") or {}
        if argument.get("kind") != "rw":
            _prewrite_error("non-'rw' argument encountered", argument)

        # RWSimpl case: `/=` or `/~=`. In `ecParser.mly` this comes from
        # the `RWSimpl` constructor of `rwarg1`, and in `ecProofAst.ml`
        # it is serialized by `json_of_rwarg1` as:
        #
        #   { "kind": "rw", "variant": "default"|"variant", ... }
        #
        # with no `options` / `entries`. We render these as `rewrite /=`
        # or `rewrite /~=` respectively.
        if "variant" in argument:
            if "options" in argument and argument.get("options"):
                _prewrite_error("RWSimpl with non-empty options", argument)
            if "entries" in argument and argument.get("entries"):
                _prewrite_error("RWSimpl with unexpected entries", argument)

            variant = argument.get("variant")
            if variant == "default":
                token = "/="
            elif variant == "variant":
                token = "/~="
            else:
                _prewrite_error(f"unknown simplification variant '{variant}'", argument)

            lines.append((_apply_target_suffix(f"rewrite {token}.", target_symbol), raw))
            continue

        # RWSmt case: `/#` or `//#` inside a rewrite. In `ecParser.mly`
        # this is `RWSmt (flag, info)`, and in `ecProofAst.ml` it is
        # serialized by `json_of_rwarg1` as:
        #
        #   { "kind": "rw", "interactive": Bool, "info": pprover_infos }
        #
        # We render it as its own rewrite line, ignoring prover options:
        #   - interactive = false → `rewrite /#.`
        #   - interactive = true  → `rewrite //#.`
        if "interactive" in argument and "info" in argument and "entries" not in argument:
            interactive = bool(argument.get("interactive"))
            token = "//#" if interactive else "/#"
            lines.append((_apply_target_suffix(f"rewrite {token}.", target_symbol), raw))
            continue

        # RWDone case: `rewrite //` / `//~=` etc. Serialized with `mode`.
        done_mode = argument.get("mode")
        if done_mode is not None and "options" not in argument and "entries" not in argument and "formula" not in argument:
            if done_mode == "default":
                token = "//"
            elif done_mode == "variant":
                token = "//~="
            else:
                _prewrite_error(f"unknown rewrite done mode '{done_mode}'", argument)
            lines.append((_apply_target_suffix(f"rewrite {token}.", target_symbol), raw))
            continue

        # RWDelta case: `rewrite /foo` or `rewrite -/foo`. In the parser,
        # this is `RWDelta ((s, r, o, None), x)`, and in `ecProofAst.ml`
        # it is serialized as:
        #
        #   { "kind": "rw", "options": {...}, "formula": {...} }
        #
        # with no `entries`. We use the `source` text and global side,
        # ignoring the bound formula and any focus.
        is_delta = "formula" in argument and "entries" not in argument

        # RWRw case coming from `rwarg1` in `ecParser.mly`, serialized as
        # `kind: "rw"` with `options` (side, repeat, occurs, guard) and
        # an `entries` list of per-lemma terms.
        is_rwrw = "entries" in argument

        if not (is_delta or is_rwrw):
            _prewrite_error(
                "rw-argument is neither RWSimpl, RWDelta, RWSmt, nor RWRw",
                argument,
            )

        options = argument.get("options")
        if not isinstance(options, dict):
            _prewrite_error("rw-argument without 'options'", argument)

        repeat = options.get("repeat")
        occurs = options.get("occurs")
        guard = options.get("guard")

        if guard not in (None, {}):
            _prewrite_error("rw-argument with guard formula", argument)

        src = (argument.get("source") or "").strip()
        if not src:
            _prewrite_error("missing 'source' text for rw-argument", argument)

        # Helper to normalize the global side encoded in `rwside` (see
        # `rwside` and `rwrepeat` in `ecParser.mly`, and `json_of_rwoptions`
        # in `ecProofAst.ml`).
        side_str = options.get("side") or "l-to-r"
        if side_str not in ("l-to-r", "r-to-l"):
            _prewrite_error(f"unexpected side '{side_str}'", argument)
        global_is_rtl = side_str == "r-to-l"

        # Simple delta rewrite: no repetition, no entries; just translate
        # the `/foo` or `-/foo` token, adjusting the leading '-' via
        # `side`.
        if is_delta:
            if repeat is not None:
                _prewrite_error("RWDelta with repetition", argument)

            token = src
            if global_is_rtl and not token.startswith("-"):
                token = f"-{token}"

            lines.append((_apply_target_suffix(f"rewrite {token}.", target_symbol), raw))
            continue

        # At this point we know we are in the RWRw case with an entries list.
        entries = argument.get("entries") or []
        if not isinstance(entries, list) or not entries:
            _prewrite_error("RWRw argument has no 'entries'", argument)

        # Simple lemma rewrites: no global repeat. We require a single
        # entry and no per-lemma side overrides, and we reuse the
        # original `source` text, only adjusting the leading '-'
        # according to `side`.
        if repeat is None:
            if len(entries) != 1:
                _prewrite_error("non-repeated rw-argument with multiple entries", argument)

            entry = entries[0]
            token = _token_from_entry(src, global_is_rtl, entry, occurs)
            lines.append((_apply_target_suffix(f"rewrite {token}.", target_symbol), raw))
            continue

        # Repeated rewrites: we currently support only the `!(...)`
        # bundle used in Pedersen, encoded in the parser as `rwrepeat`
        # with mode `All` (JSON `mode: "all"`) and no explicit count.
        mode = repeat.get("mode") if isinstance(repeat, dict) else None
        count = repeat.get("count") if isinstance(repeat, dict) else None
        if mode != "all":
            _prewrite_error("only 'all' repetitions are handled", argument)

        if count is not None:
            if len(entries) != 1:
                _prewrite_error("counted repeated rewrites must have a single entry", argument)
            entry = entries[0]
            token = _token_from_entry(src, global_is_rtl, entry, occurs)
            for _ in range(int(count)):
                lines.append((_apply_target_suffix(f"rewrite {token}.", target_symbol), raw))
            continue

        # Each entry corresponds to one lemma inside the `!(...)`
        # group. We synthesize the per-lemma direction from the global
        # side (rwside) and the entry side (rwpterm), as defined in
        # `rwside` / `rwpterm` in `ecParser.mly` and serialized by
        # `json_of_rwarg1` in `ecProofAst.ml`.
        for entry in entries:
            if not isinstance(entry, dict):
                _prewrite_error("malformed entry in repeated rw-argument", entry)

            entry_side = entry.get("side") or "l-to-r"
            if entry_side not in ("l-to-r", "r-to-l"):
                _prewrite_error(f"unexpected entry side '{entry_side}'", entry)

            # Composition of global and per-entry side:
            entry_is_rtl = entry_side == "r-to-l"
            final_is_rtl = global_is_rtl ^ entry_is_rtl

            term = entry.get("term") or {}
            if term.get("mode") != "implicit":
                _prewrite_error("non-implicit term in repeated rw-argument", entry)
            head = term.get("head") or {}
            if head.get("kind") != "named":
                _prewrite_error("non-named head in repeated rw-argument", entry)
            name = head.get("name")
            args_list = head.get("args") or []
            if not isinstance(name, str) or not name:
                _prewrite_error("missing lemma name in repeated rw-argument", entry)
            if args_list:
                _prewrite_error("lemma applications in repeated rw-argument", entry)

            prefix = "-!" if final_is_rtl else "!"
            lines.append((_apply_target_suffix(f"rewrite {prefix}{name}.", target_symbol), raw))

    return lines


def _render_prewrite_tactic(core: dict) -> str:
    lines = _collect_prewrite_lines(core)
    return "\n".join(text for text, _ in lines) if lines else ""


def extract_tactic_text(tactic: dict) -> str | None:
    core = tactic.get("core", {}) or {}

    # Prefer the structured representation for `Prewrite` so we can
    # split bundled rewrites into separate lines. If we encounter a
    # shape we do not understand while doing so, `_render_prewrite_tactic`
    # will raise `SystemExit` to abort instead of guessing.
    tactic_info = (core.get("args") or {}).get("tactic") or {}
    if tactic_info.get("kind") == "Prewrite":
        return _render_prewrite_tactic(core)

    text = core.get("source")
    if isinstance(text, str):
        text = text.strip()
    return text or None


def render_intro_token(token: dict) -> str:
    kind = token.get("kind")
    if kind == "case":
        return render_case_pattern(token)
    if kind == "named":
        name = token.get("name")
        if isinstance(name, str) and name.strip():
            return name.strip()
    if kind == "revert":
        return "+"
    if kind == "clear":
        return "_"
    if kind == "anonymous":
        return "?"
    if kind == "break":
        return "-"
    if kind == "dup":
        return "dup"
    if kind == "clear-names":
        names = token.get("names") or []
        if isinstance(names, list) and names:
            formatted = " ".join(str(name).strip() for name in names if str(name).strip())
            if formatted:
                return f"{{{formatted}}}"
    if kind == "rw":
        direction = token.get("direction")
        if direction == "rtl":
            return "<-"
        return "->"
    if kind == "done":
        variant = token.get("variant")
        if variant == "variant":
            return "//~="
        if variant == "default":
            return "//="
        return "//"
    if kind == "simplify":
        variant = token.get("variant")
        return "/~=" if variant == "variant" else "/="
    if kind == "smt":
        loud = bool(token.get("loud"))
        return "//#" if loud else "/#"
    if kind == "crush":
        simplify = bool(token.get("simplify"))
        solve = bool(token.get("solve"))
        if simplify and solve:
            return "//>"
        if simplify:
            return "/>"
        if solve:
            return "||>"
        return "|>"
    source = token.get("source")
    if isinstance(source, str):
        source = source.strip()
        if source:
            return source
    fallback = kind or "_"
    print(f"[formatter] Warning: unsupported intro pattern token {token}", file=sys.stderr)
    return fallback


def _sorted_indices(values: Sequence[int]) -> List[int]:
    return sorted(int(v) for v in values)


def is_trivial_serialized(serialized: Sequence[dict] | None) -> bool:
    if not serialized:
        return True
    relevant = False
    for entry in serialized:
        incoming = _sorted_indices(entry.get("in") or [])
        outgoing = _sorted_indices(entry.get("out") or [])
        if incoming or outgoing:
            relevant = True
        if incoming != outgoing:
            return False
    return relevant


def render_case_pattern(token: dict) -> str:
    patterns = token.get("patterns") or []

    def iter_entries(entry: dict | Sequence) -> Iterable[dict]:
        if isinstance(entry, dict):
            yield entry
            return
        if isinstance(entry, (list, tuple)):
            for nested in entry:
                yield from iter_entries(nested)

    branches: List[str] = []
    for branch in patterns:
        entries = list(iter_entries(branch))
        parts = [render_intro_token(entry) for entry in entries]
        text = " ".join(part for part in parts if part)
        branches.append(text or "#")
    if not branches:
        return "[#]"
    inner = " | ".join(branches)
    return f"[ {inner} ]"


def intro_entry_to_text(intro: dict) -> str | None:
    kind = intro.get("kind")
    if kind == "intros":
        pattern = intro.get("pattern") or []
        parts = [render_intro_token(token) for token in pattern]
        suffix = " ".join(part for part in parts if part)
        return f"move=> {suffix}".rstrip()
    if kind == "generalize":
        revert = intro.get("revert") or {}
        clear = " ".join(revert.get("clear") or [])
        generators = revert.get("generators")
        suffix = " ".join(part for part in [clear, f"gen[{generators}]" if generators else ""] if part)
        text = suffix.strip()
        if text:
            return f"move=> {text}"
        return "move=>"
    print(f"[formatter] Warning: unsupported intro entry {intro}", file=sys.stderr)
    return None


def intro_token_to_text(token: dict) -> str | None:
    kind = token.get("kind")
    if kind == "generalize":
        revert = token.get("revert") or {}
        clear = revert.get("clear") or []
        clear_text = " ".join(str(name).strip() for name in clear if str(name).strip())
        generators = revert.get("generators")
        parts = [clear_text]
        if isinstance(generators, int) and generators > 0:
            parts.append(f"gen[{generators}]")
        suffix = " ".join(part for part in parts if part).strip()
        return f"move=> {suffix}".rstrip() if suffix else "move=>"
    token_text = render_intro_token(token)
    if token_text:
        return f"move=> {token_text}".rstrip()
    return None


def _intro_tail_connectors(intro: dict) -> List[Sequence[dict]]:
    tokens = intro.get("pattern") or []
    if not tokens:
        return []

    token_inputs: List[set[int]] = []
    for token in tokens:
        inputs: set[int] = set()
        for entry in token.get("serialized_goals") or []:
            for goal in entry.get("in") or []:
                inputs.add(int(goal))
        token_inputs.append(inputs)

    suffix_consumers: List[set[int]] = [set() for _ in tokens]
    future_inputs: set[int] = set()
    for idx in range(len(tokens) - 1, -1, -1):
        suffix_consumers[idx] = set(future_inputs)
        future_inputs.update(token_inputs[idx])

    tails: List[int] = []
    for idx, token in enumerate(tokens):
        future = suffix_consumers[idx]
        for entry in token.get("serialized_goals") or []:
            for goal in entry.get("out") or []:
                goal_id = int(goal)
                if goal_id not in future and goal_id not in tails:
                    tails.append(goal_id)

    block_outs: List[int] = []
    for entry in intro.get("serialized_goals") or []:
        block_outs.extend(int(goal) for goal in entry.get("out") or [])

    connectors: List[Sequence[dict]] = []
    for src, dst in zip(tails, block_outs):
        if src == dst:
            continue
        connectors.append([{"in": [src], "out": [dst]}])

    return connectors


def _warn_intro_gap(
    intro: dict, token: dict, missing: Sequence[int], reachable: Sequence[int], block_inputs: Sequence[int]
) -> None:
    if not missing:
        return
    source = token.get("source") or token.get("snippet") or token.get("kind") or "unknown"
    print(
        "[formatter] Warning: intro token '{source}' consumes goals {missing} "
        "that were never produced within its block (reachable so far {reachable}, block inputs {block_inputs})".format(
            source=source,
            missing=list(missing),
            reachable=list(reachable),
            block_inputs=list(block_inputs),
        ),
        file=sys.stderr,
    )


def _flatten_intro_patterns(entries: Sequence[dict | Sequence]) -> List[dict]:
    flattened: List[dict] = []
    for entry in entries:
        if isinstance(entry, dict):
            flattened.append(entry)
            continue
        if isinstance(entry, list):
            flattened.extend(_flatten_intro_patterns(entry))
    return flattened


def iter_intro_elements(intro: dict) -> Iterable[Tuple[str | None, Sequence[dict]]]:
    tokens = _flatten_intro_patterns(intro.get("pattern") or [])
    if tokens:
        has_bridge = any((token.get("kind") or "").lower() == "bridge" for token in tokens)
        if has_bridge:
            for token in tokens:
                kind = (token.get("kind") or "").lower()
                serialized = token.get("serialized_goals") or []
                if kind == "bridge":
                    if serialized and not is_trivial_serialized(serialized):
                        yield None, serialized
                    continue
                text = intro_token_to_text(token)
                if text and not is_trivial_serialized(serialized):
                    yield text, serialized
            return
        block_inputs = {
            int(goal)
            for entry in intro.get("serialized_goals") or []
            for goal in entry.get("in") or []
        }
        reachable = set(block_inputs)
        for token in tokens:
            text = intro_token_to_text(token)
            serialized = token.get("serialized_goals") or []
            token_inputs = {
                int(goal)
                for entry in serialized
                for goal in entry.get("in") or []
            }
            missing = sorted(goal for goal in token_inputs if goal not in reachable)
            if missing:
                _warn_intro_gap(intro, token, missing, sorted(reachable), sorted(block_inputs))
            if text and not is_trivial_serialized(serialized):
                yield text, serialized
            for entry in serialized:
                for goal in entry.get("out") or []:
                    reachable.add(int(goal))
        for connector in _intro_tail_connectors(intro):
            if connector and not is_trivial_serialized(connector):
                yield None, connector
        return

    intro_text = intro_entry_to_text(intro)
    intro_serialized = intro.get("serialized_goals") or []
    if intro_text and not is_trivial_serialized(intro_serialized):
        yield intro_text, intro_serialized


def _prepare_pby_children(entry: dict) -> List[dict]:
    core = entry.get("core", {}) or {}
    script_entries = core.get("args", {}).get("script") or []
    prepared: List[dict] = [_normalize_child_entry(sub) for sub in script_entries]
    if not prepared:
        return prepared

    last = prepared[-1]
    serialized = last.get("serialized_goals") or []
    needs_trivial = any(entry.get("out") for entry in serialized if entry.get("out"))
    if needs_trivial:
        close_entries: List[dict] = []
        for mapping in serialized:
            outs = mapping.get("out") or []
            if not outs:
                continue
            close_entries.append({"in": list(outs), "out": []})
        if close_entries:
            prepared.append(
                {
                    "core": {"node": "Pdone", "source": "trivial"},
                    "serialized_goals": close_entries,
                }
            )
    return prepared


def _normalize_child_entry(entry: dict) -> dict:
    if "core" in entry:
        return dict(entry)
    wrapped = dict(entry)
    core: dict = {}
    for key in ("node", "source", "args", "children"):
        if key in wrapped:
            core[key] = wrapped.pop(key)
    wrapped["core"] = core
    return wrapped


def iter_child_entries(entry: dict) -> List[dict]:
    core = entry.get("core", {}) or {}
    node = core.get("node")
    if node == "Pby":
        return _prepare_pby_children(entry)
    if node == "Pdo":
        return []

    children: List[dict] = [_normalize_child_entry(child) for child in core.get("children") or []]

    args = core.get("args")
    chain = args.get("chain") if isinstance(args, dict) else None
    if chain:
        children.extend(_normalize_child_entry(child) for child in chain.get("tactics") or [])
        for target in chain.get("targets") or []:
            tactic = target.get("tactic")
            if tactic:
                children.append(_normalize_child_entry(tactic))
        fallback = chain.get("fallback")
        if fallback:
            children.append(_normalize_child_entry(fallback))
        direct = chain.get("tactic")
        if direct:
            children.append(_normalize_child_entry(direct))

    return children


def iter_tactic_entries(
    entry: dict,
    inherited: Sequence[dict] | None = None,
) -> Iterable[Tuple[str | None, Sequence[dict]]]:
    core = entry.get("core", {}) or {}
    raw_serialized = entry.get("serialized_goals")
    serialized = raw_serialized or inherited or []

    children = iter_child_entries(entry)
    yielded_child = False
    for child in children:
        for nested in iter_tactic_entries(child, serialized):
            yielded_child = True
            yield nested
    if yielded_child:
        # Children already emitted, but intros attached to this node may still
        # carry serialized goal mappings (e.g., bridges). Surface them so goal
        # production/consumption stays accurate.
        for intro in entry.get("intros") or []:
            for text, serialized_intro in iter_intro_elements(intro):
                yield text, serialized_intro
        return

    tactic_info = (core.get("args") or {}).get("tactic") or {}
    if tactic_info.get("kind") == "Prewrite":
        fallback_serialized = raw_serialized or inherited or []
        yielded_pw = False
        for text, raw_arg in _collect_prewrite_lines(core):
            serialized_arg = raw_arg.get("serialized_goals") or fallback_serialized
            if text and not is_trivial_serialized(serialized_arg):
                yield text, serialized_arg
                yielded_pw = True
        # Even if no rewrite lines were yielded, we may still have intros
        # attached to this Prewrite node that carry serialized goal mappings.
        for intro in entry.get("intros") or []:
            for text, serialized_intro in iter_intro_elements(intro):
                yield text, serialized_intro
        return

    text = extract_tactic_text(entry)
    effective_serialized = raw_serialized or []
    if text and not is_trivial_serialized(effective_serialized):
        yield text, serialized

    for intro in entry.get("intros") or []:
        for text, serialized_intro in iter_intro_elements(intro):
            yield text, serialized_intro


def iter_lemma_tactics(lemma: dict) -> Iterable[Tuple[str | None, Sequence[dict]]]:
    for block in lemma.get("blocks", []):
        if block.get("index") == 0:
            continue
        for tactic in block.get("tactics", []):
            yield from iter_tactic_entries(tactic)


def _warn_disconnected_goals(
    lemma_name: str | None, goal_consumers: Dict[int, List[TacticOccurrence]], produced: set[int]
) -> None:
    if not goal_consumers:
        return

    inputs = set(goal_consumers.keys())
    roots = sorted(inputs - produced)
    if not roots:
        return

    baseline = roots[0]
    for goal in roots:
        if goal == baseline:
            continue
        occs = goal_consumers.get(goal, [])
        if not occs:
            continue
        excerpts = ", ".join(
            f"[{occ.idx}] {occ.text or '<no-op>'} -> {occ.outputs or []}" for occ in occs[:3]
        )
        extra = "" if len(occs) <= 3 else f" (+{len(occs) - 3} more)"
        prefix = f"[formatter] Warning: lemma '{lemma_name}'" if lemma_name else "[formatter] Warning"
        print(
            f"{prefix}: goal {goal} has consumers but no producer; sequence heads: {excerpts}{extra}",
            file=sys.stderr,
        )


def collect_goal_occurrences(lemma: dict, lemma_name: str | None = None) -> Dict[int, List[TacticOccurrence]]:
    goal_consumers: Dict[int, List[TacticOccurrence]] = defaultdict(list)
    occurrence_idx = 0
    produced: set[int] = set()

    for text, serialized in iter_lemma_tactics(lemma):
        entries = [entry for entry in serialized if entry.get("in")]
        if not entries:
            continue

        for entry in entries:
            inputs = entry.get("in") or []
            outputs = entry.get("out") or []
            assignments = assign_outputs(inputs, outputs)
            for goal, child_goals in assignments:
                occurrence_idx += 1
                goal_consumers[goal].append(
                    TacticOccurrence(
                        idx=occurrence_idx,
                        goal=goal,
                        text=text,
                        outputs=list(child_goals),
                    )
                )
                produced.update(child_goals)

    _warn_disconnected_goals(lemma_name, goal_consumers, produced)
    return goal_consumers


def traverse_goal_graph(goal_consumers: Dict[int, List[TacticOccurrence]]) -> List[TacticOccurrence]:
    if not goal_consumers:
        return []

    produced = {goal for occs in goal_consumers.values() for occ in occs for goal in occ.outputs}
    inputs = set(goal_consumers.keys())
    roots = sorted(inputs - produced) or sorted(inputs)

    sequence: List[TacticOccurrence] = []
    visited: set[int] = set()
    processed_goals: set[int] = set()

    def dfs(goal: int) -> None:
        if goal in processed_goals:
            return
        processed_goals.add(goal)
        occs = sorted(goal_consumers.get(goal, []), key=lambda o: o.idx)
        for occ in occs:
            if occ.idx in visited:
                continue
            visited.add(occ.idx)
            sequence.append(occ)
        for occ in occs:
            for child in occ.outputs:
                if child in goal_consumers:
                    dfs(child)

    for root in roots:
        dfs(root)

    total = sum(len(occs) for occs in goal_consumers.values())
    if len(sequence) != total:
        leftovers = [
            occ
            for occs in goal_consumers.values()
            for occ in occs
            if occ.idx not in visited
        ]
        for occ in sorted(leftovers, key=lambda o: o.idx):
            visited.add(occ.idx)
            sequence.append(occ)

    return sequence


def build_tactic_sequence(lemma: dict) -> List[str]:
    """
    Build a linearized list of tactic strings for a lemma based on its
    serialized goal graph.
    """
    consumers = collect_goal_occurrences(lemma, lemma.get("name"))
    ordered = traverse_goal_graph(consumers)
    return [occ.text for occ in ordered if occ.text]


def lemma_goal_graph(lemma: dict) -> List[dict]:
    """
    Return the DFS goal graph (in traversal order) for a lemma.

    Each entry contains:
      - idx: occurrence index in the serialized trace
      - goal: input goal id
      - outputs: produced goal ids
      - text: tactic text (may be None)
    """
    consumers = collect_goal_occurrences(lemma, lemma.get("name"))
    ordered = traverse_goal_graph(consumers)
    return [
        {
            "idx": occ.idx,
            "goal": occ.goal,
            "outputs": list(occ.outputs),
            "text": occ.text,
        }
        for occ in ordered
    ]


def format_tactic_lines(tactics: Sequence[str], body_indent: str) -> List[str]:
    formatted: List[str] = []
    for i, tactic in enumerate(tactics):
        suffix = "."
        text = tactic.strip()
        if not text:
            continue
        lines = [segment.rstrip() for segment in text.splitlines()]
        for j, line in enumerate(lines):
            token = f"{body_indent}{line}"
            if j == len(lines) - 1 and not line.endswith("."):
                token = f"{token}{suffix}"
            formatted.append(token)
    return formatted


def ensure_newline(block: str) -> str:
    if not block:
        return ""
    return block if block.endswith("\n") else f"{block}\n"


def indent_statement(statement: str, indent: str) -> str:
    if not statement:
        return ""
    lines = statement.splitlines()
    head = f"{indent}{lines[0].lstrip()}"
    return "\n".join([head] + lines[1:])


def indent_block(text: str, indent: str) -> str:
    if not text:
        return ""
    lines = text.splitlines()
    return "\n".join(f"{indent}{line}" if line else indent for line in lines)


def find_statement_indent(source_text: str, start: int, statement: str) -> Tuple[str, int]:
    first_line = statement.splitlines()[0].lstrip() if statement else ""
    if not first_line:
        return "", start

    pattern = re.compile(rf"(?m)^([ \t]*){re.escape(first_line)}")
    match = pattern.search(source_text, start)
    if not match:
        return "", start
    return match.group(1), match.end()


def render_existing_lemma(statement: str, proof: str, indent: str) -> str:
    stmt = indent_statement(statement, indent)
    proof_block = indent_block(proof, indent)
    return "\n".join(filter(None, [stmt, proof_block]))


def render_formatted_lemma(statement: str, indent: str, tactics: Sequence[str]) -> str:
    stmt = indent_statement(statement, indent)
    body_indent = indent + "  "
    tactic_lines = format_tactic_lines(tactics, body_indent)
    proof_lines = [f"{indent}proof.", *tactic_lines, f"{indent}qed."]
    return "\n".join([stmt] + proof_lines)


def rewrite_file(
    path: Path,
    updates: Sequence[Tuple[str, List[str]]],
    available_lemmas: Sequence[str],
    suppress_mismatch_warnings: bool = False,
) -> Tuple[str, List[str]]:
    try:
        parsed = parse_easycrypt.parse_easycrypt_file(path)
    except Exception as err:  # pragma: no cover - passthrough for parser errors
        raise SystemExit(f"Failed to parse EasyCrypt file {path}: {err}") from err

    try:
        source_text = path.read_text()
    except OSError as err:
        raise SystemExit(f"Failed to read EasyCrypt file {path}: {err}") from err

    update_map = {name: tactics for name, tactics in updates}
    available = set(available_lemmas)
    applied: List[str] = []
    cursor = 0
    chunks: List[str] = []

    parsed_lemmas: List[str] = []

    for entry in parsed.get("content", []):
        entry_type = entry.get("type")
        if entry_type not in {"lemma", "axiom"}:
            chunks.append(entry.get("content", ""))
            continue

        statement = entry.get("statement", "")
        indent, cursor = find_statement_indent(source_text, cursor, statement)

        if entry_type == "axiom":
            chunks.append(indent_statement(statement, indent))
            continue

        name = entry.get("name")
        parsed_lemmas.append(name)
        proof = entry.get("proof", "")
        tactics = update_map.get(name)
        if tactics:
            chunks.append(render_formatted_lemma(statement, indent, tactics))
            applied.append(name)
        else:
            chunks.append(render_existing_lemma(statement, proof, indent))

    if not suppress_mismatch_warnings:
        missing_in_ast = sorted(name for name in parsed_lemmas if name not in available)
        if missing_in_ast:
            print(
                "[formatter] Warning: lemmas missing from AST: "
                + ", ".join(missing_in_ast),
                file=sys.stderr,
            )

        missing_in_parser = sorted(name for name in available if name not in parsed_lemmas)
        if missing_in_parser:
            print(
                "[formatter] Warning: lemmas present in AST but not parser output: "
                + ", ".join(missing_in_parser),
                file=sys.stderr,
            )

        missing = sorted(name for name in update_map if name not in applied)
        for name in missing:
            print(
                f"[formatter] Warning: lemma '{name}' not found in {path}; keeping existing proof",
                file=sys.stderr,
            )

    text = "".join(ensure_newline(chunk) for chunk in chunks)
    if not text.endswith("\n"):
        text += "\n"
    return text, applied


def format_lemmas(
    easycrypt_file: str | Path,
    ast_file: str | Path,
    lemma_names: Sequence[str] | None = None,
    suppress_mismatch_warnings: bool = False,
    dump_graph_path: Path | None = None,
) -> Tuple[Path, Dict[str, int]]:
    """
    Format one or more lemmas in `easycrypt_file` using the proof AST in
    `ast_file`.

    Returns:
        (formatted_file_path, {lemma_name: tactic_count_after_formatting})
    """
    ec_path = Path(easycrypt_file)
    ast_path = Path(ast_file)

    lemmas, lemma_order = load_ast(ast_path)
    if not lemmas:
        raise SystemExit("No lemmas found in AST.")

    targets = set(lemma_names) if lemma_names else set(lemmas.keys())
    unknown = targets - set(lemmas.keys())
    if unknown:
        raise SystemExit(f"Lemmas not found in AST: {', '.join(sorted(unknown))}")

    ordered_targets = [name for name in lemma_order if name in targets]

    updates: List[Tuple[str, List[str]]] = []
    graphs: Dict[str, List[dict]] = {}
    tactic_counts: Dict[str, int] = {}
    for name in ordered_targets:
        seq = build_tactic_sequence(lemmas[name])
        if dump_graph_path is not None:
            graphs[name] = lemma_goal_graph(lemmas[name])
        tactic_counts[name] = len(seq)
        if seq:
            updates.append((name, seq))

    if not updates:
        raise SystemExit("No tactic sequences produced; nothing to do.")

    formatted_text, applied = rewrite_file(
        ec_path, updates, lemmas.keys(), suppress_mismatch_warnings=suppress_mismatch_warnings
    )
    if not applied:
        raise SystemExit("No lemmas were updated; aborting to avoid writing output.")

    output_path = ec_path.with_suffix(".formatted.ec")
    try:
        output_path.write_text(formatted_text)
    except OSError as err:
        raise SystemExit(f"Failed to write formatted file {output_path}: {err}") from err

    if dump_graph_path is not None:
        graph_payload = {name: graphs.get(name, []) for name in ordered_targets}
        try:
            dump_graph_path = Path(dump_graph_path)
            dump_graph_path.write_text(json.dumps(graph_payload, indent=2, sort_keys=True))
        except OSError as err:
            raise SystemExit(f"Failed to write graph file {dump_graph_path}: {err}") from err

    return output_path, {name: tactic_counts.get(name) for name in applied}


def main() -> None:
    """CLI entrypoint; preserved for backwards compatibility."""
    args = parse_args()
    try:
        output_path, tactic_counts = format_lemmas(
            args.easycrypt_file,
            args.ast_file,
            args.lemmas,
            dump_graph_path=Path(args.dump_graph) if args.dump_graph else None,
        )
    except SystemExit as err:
        # Re-raise SystemExit so CLI exit codes remain meaningful.
        raise
    except Exception as err:  # pragma: no cover - passthrough for unexpected errors
        raise SystemExit(f"Formatter failed: {err}") from err

    if not tactic_counts:
        raise SystemExit("No lemmas were updated; aborting to avoid writing output.")

    applied = sorted(tactic_counts.keys())
    print(f"[formatter] Updated lemmas: {', '.join(applied)}")
    print(
        "[formatter] Tactics per lemma: "
        + ", ".join(f"{name}={tactic_counts[name]}" for name in applied)
    )
    print(f"[formatter] Wrote {output_path}")


if __name__ == "__main__":
    main()

