from __future__ import annotations

import argparse
import json
import re
from collections import defaultdict, deque
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Set, Tuple

from .lexer_extractor import TokenInfo, extract_lexer_info


MACRO_NAMES: Set[str] = {
    "plist0",
    "plist1",
    "plist2",
    "rlist0",
    "rlist1",
    "rlist2",
    "iplist1",
    "iplist1_r",
    "__rlist1",
    "list2",
    "paren",
    "brace",
    "bracket",
    "seq",
    "prefix",
    "prefix1",
    "postfix",
    "sep",
    "either",
    "or3",
    "loc",
    "iboption",
    "ioption",
    "uoption",
    "boption",
    "option",
    "ior_",
    "ID",
}

COLLAPSE_MAP = {
    "form": "FORM_TERM",
    "form_r": "FORM_TERM",
    "form_u": "FORM_TERM",
    "sform": "FORM_TERM",
    "sform_r": "FORM_TERM",
    "sform_u": "FORM_TERM",
    "form_h": "FORM_TERM",
    "form_ordering": "FORM_TERM",
    "form_chained_orderings": "FORM_TERM",
    "form_field": "FORM_TERM",
    "expr": "EXPR_TERM",
    "stmt": "STMT_TERM",
    "block": "STMT_TERM",
    "base_instr": "STMT_TERM",
    "namespace": "QIDENT_TERM",
    "_genqident": "QIDENT_TERM",
    "genqident": "QIDENT_TERM",
    "gpoterm": "TERM_TERM",
    "gpterm_arg": "TERM_TERM",
    "gpoterm_head": "TERM_TERM",
    "gpterm_head": "TERM_TERM",
    "pcutdef": "FORM_TERM",
    "pcutdef1": "FORM_TERM",
    "ptype": "TYPE_TERM",
    "type_exp": "TYPE_TERM",
    "ptybindings": "BIND_TERM",
    "ptybinding1": "BIND_TERM",
    "pty_varty": "BIND_TERM",
    "pgtybindings": "BIND_TERM",
    "tvars_app": "TARG_TERM",
    "rwpterm": "TERM_TERM",
    "rwpterms": "TERM_TERM",
    "rwpr_arg": "TERM_TERM",
    "rwside": "TERM_TERM",
    "rwrepeat": "TERM_TERM",
    "rwocc": "TERM_TERM",
    "gpterm": "TERM_TERM",
    "gpterm_head": "TERM_TERM",
    "igpterm_arg": "TERM_TERM",
    "igpterm": "TERM_TERM",
}
COLLAPSE_PATTERN = (
    re.compile(r"\b(" + "|".join(map(re.escape, COLLAPSE_MAP.keys())) + r")\b")
    if COLLAPSE_MAP
    else None
)
def main() -> None:
    parser = argparse.ArgumentParser(
        description="Convert EasyCrypt tactic grammar (from JSON) to EBNF."
    )
    parser.add_argument(
        "--json",
        type=Path,
        default=Path("out/grammar_raw.json"),
        help="Path to the Menhir-extracted grammar JSON file.",
    )
    parser.add_argument(
        "--lexer",
        type=Path,
        default=Path("src/ecLexer.mll"),
        help="Path to ecLexer.mll for enriching terminal metadata.",
    )
    parser.add_argument(
        "--out-ebnf",
        type=Path,
        default=Path("out/easycrypt_tactic.ebnf"),
        help="Destination EBNF file.",
    )
    parser.add_argument(
        "--start",
        default="tactic",
        help="Start nonterminal to retain before wrapping into Line ::= start '.'",
    )
    args = parser.parse_args()

    data = json.loads(args.json.read_text())
    parser_tokens: Set[str] = set(data["parser"]["tokens"])
    placeholder_tokens = set(COLLAPSE_MAP.values())
    productions_raw = [
        prod
        for prod in expand_inline_alternatives(data["parser"]["productions"])
        if prod["head"] not in MACRO_NAMES and prod["head"] not in COLLAPSE_MAP
    ]

    nonterminals = {
        prod["head"]
        for prod in productions_raw
        if prod["head"] not in MACRO_NAMES and prod["head"] not in COLLAPSE_MAP
    }
    reachable = compute_reachable(args.start, productions_raw, nonterminals)
    restricted = [
        prod
        for prod in productions_raw
        if prod["head"] in reachable
    ]

    transformed = transform_bodies(restricted)

    token_metadata = extract_lexer_info(args.lexer).tokens
    for placeholder in placeholder_tokens:
        if placeholder not in token_metadata:
            token_metadata[placeholder] = TokenInfo(name=placeholder, pattern=".+")
    used_tokens = collect_terminals(transformed, parser_tokens, placeholder_tokens)
    ebnf = render_ebnf(transformed, used_tokens, token_metadata, args.start)

    args.out_ebnf.parent.mkdir(parents=True, exist_ok=True)
    args.out_ebnf.write_text(ebnf)

    print(f"Wrote {args.out_ebnf} with {len(transformed)} tactic productions.")


def expand_inline_alternatives(
    productions: Sequence[Dict[str, object]]
) -> List[Dict[str, str]]:
    expanded: List[Dict[str, str]] = []
    for prod in productions:
        head = prod["head"]
        body = prod["body"].strip()
        parts = split_top_level_alts(body)
        for part in parts:
            expanded.append({"head": head, "body": part.strip()})
    return expanded


def split_top_level_alts(text: str) -> List[str]:
    parts: List[str] = []
    current: List[str] = []
    depth = 0
    i = 0
    while i < len(text):
        char = text[i]
        if char == "(":
            depth += 1
        elif char == ")":
            depth = max(0, depth - 1)
        if char == "|" and depth == 0:
            segment = "".join(current).strip()
            if segment:
                parts.append(segment)
            current = []
        else:
            current.append(char)
        i += 1
    tail = "".join(current).strip()
    if tail:
        parts.append(tail)
    return parts


def compute_reachable(
    start: str,
    productions: Sequence[Dict[str, str]],
    nonterminals: Set[str],
) -> Set[str]:
    refs_by_head: Dict[str, List[str]] = defaultdict(list)
    bodies_by_head: Dict[str, List[str]] = defaultdict(list)
    for prod in productions:
        body = prod["body"]
        bodies_by_head[prod["head"]].append(body)
        for sym in extract_symbols(body):
            if sym in nonterminals:
                refs_by_head[prod["head"]].append(sym)

    reachable: Set[str] = set()
    queue: deque[str] = deque([start])

    while queue:
        head = queue.popleft()
        if head in reachable:
            continue
        reachable.add(head)
        for sym in refs_by_head.get(head, []):
            if sym not in reachable:
                queue.append(sym)

    # ensure epsilon helpers reachable from start exist even without outbound edges
    for head in list(reachable):
        for body in bodies_by_head.get(head, []):
            for sym in extract_symbols(body):
                if sym in nonterminals and sym not in reachable:
                    queue.append(sym)
        while queue:
            sym = queue.popleft()
            if sym in reachable:
                continue
            reachable.add(sym)
            queue.extend(refs_by_head.get(sym, []))

    return reachable


WORD_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")


def extract_symbols(body: str) -> List[str]:
    return WORD_RE.findall(body)


def transform_bodies(productions: Sequence[Dict[str, str]]) -> Dict[str, List[str]]:
    result: Dict[str, List[str]] = defaultdict(list)
    for prod in productions:
        cleaned = normalize_body(prod["body"])
        if cleaned is None:
            continue
        result[prod["head"]].append(cleaned)
    return result


def normalize_body(body: str) -> str | None:
    text = remove_bindings(body)
    text = strip_percent_directives(text)
    text = text.strip()
    if not text or text == "/* empty */":
        return "/* empty */"
    text = expand_macros(text)
    text = strip_param_calls(text)
    text = collapse_nonterms(text)
    text = re.sub(r"\s+", " ", text).strip()
    return text or "/* empty */"


BINDING_RE = re.compile(r"\b[A-Za-z_][A-Za-z0-9_']*\s*=")


def remove_bindings(text: str) -> str:
    return BINDING_RE.sub("", text)


def strip_percent_directives(text: str) -> str:
    text = re.sub(r"%prec\s+[A-Za-z0-9_]+", "", text)
    text = text.replace("%inline", "")
    text = text.replace("%public", "")
    text = text.replace("%token", "")
    text = re.sub(r"\s+", " ", text)
    return text


def expand_macros(text: str) -> str:
    macro_handlers = [
        ("loc", lambda args: args[0]),
        ("paren", lambda args: f'("(" {args[0]} ")")'),
        ("brace", lambda args: f'("{{" {args[0]} "}}")'),
        ("bracket", lambda args: f'("[" {args[0]} "]")'),
        ("prefix", lambda args: f"{args[0]} {args[1]}"),
        ("postfix", lambda args: f"{args[0]} {args[1]}"),
        ("plist2", expand_list2),
        ("rlist2", expand_list2),
        ("plist1", expand_list1),
        ("rlist1", expand_list1),
        ("plist0", expand_list0),
        ("rlist0", expand_list0),
        ("iboption", expand_option),
        ("ioption", expand_option),
        ("uoption", expand_option),
        ("boption", expand_option),
        ("option", expand_option),
        ("prefix1", lambda args: f"{args[0]} {args[1]}"),
        ("sep", expand_sep),
    ]

    changed = True
    while changed:
        changed = False
        for name, handler in macro_handlers:
            new_text = replace_macro(text, name, handler)
            if new_text != text:
                changed = True
                text = new_text
    return text


PARAM_CALL_RE = re.compile(r"([A-Za-z_][A-Za-z0-9_']*)\s*\(([^()]*?)\)")


def strip_param_calls(text: str) -> str:
    while True:
        replaced = False

        def repl(match: re.Match[str]) -> str:
            nonlocal replaced
            name = match.group(1)
            args = match.group(2).strip()
            if name in MACRO_NAMES:
                return match.group(0)
            if args in {"", "?", "P", "F", "F?", "hole", "none"}:
                replaced = True
                return name
            if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", args):
                replaced = True
                return name
            return match.group(0)

        new_text = PARAM_CALL_RE.sub(repl, text)
        if not replaced:
            return text
        text = new_text


def collapse_nonterms(text: str) -> str:
    if not COLLAPSE_PATTERN:
        return text
    return COLLAPSE_PATTERN.sub(lambda m: COLLAPSE_MAP[m.group(0)], text)


def expand_list1(args: Sequence[str]) -> str:
    if len(args) != 2:
        return " ".join(args)
    item, sep = args
    return f"{item} ({sep} {item})*"


def expand_list0(args: Sequence[str]) -> str:
    if len(args) != 2:
        return " ".join(args)
    item, sep = args
    return f"({item} ({sep} {item})*)?"


def expand_list2(args: Sequence[str]) -> str:
    if len(args) != 2:
        return " ".join(args)
    item, sep = args
    return f"{item} {sep} {item} ({sep} {item})*"


def expand_option(args: Sequence[str]) -> str:
    if not args:
        return ""
    return f"({args[0]})?"


def expand_sep(args: Sequence[str]) -> str:
    if len(args) != 3:
        return " ".join(args)
    return f"{args[0]} {args[1]} {args[2]}"


def replace_macro(text: str, name: str, handler) -> str:
    pattern = re.compile(rf"{name}\s*\(")
    pos = 0
    pieces: List[str] = []
    replaced = False
    while True:
        match = pattern.search(text, pos)
        if not match:
            pieces.append(text[pos:])
            break
        pieces.append(text[pos:match.start()])
        try:
            inner, end = extract_parenthesized(text, match.end() - 1)
        except ValueError as exc:
            raise ValueError(f"while expanding {name}: {exc}") from exc
        args = split_args(inner)
        pieces.append(handler(args))
        pos = end
        replaced = True
    return "".join(pieces) if replaced else text


def extract_parenthesized(text: str, open_index: int) -> Tuple[str, int]:
    assert text[open_index] == "("
    depth = 1
    i = open_index + 1
    start = i
    while i < len(text):
        char = text[i]
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
            if depth == 0:
                return text[start:i], i + 1
        i += 1
    raise ValueError(f"Unmatched '(' in: {text[open_index:open_index+40]}")


def split_args(args_text: str) -> List[str]:
    args: List[str] = []
    depth = 0
    current: List[str] = []
    i = 0
    while i < len(args_text):
        char = args_text[i]
        if char == "(":
            depth += 1
            current.append(char)
        elif char == ")":
            depth -= 1
            current.append(char)
        elif char == "," and depth == 0:
            args.append("".join(current).strip())
            current = []
        else:
            current.append(char)
        i += 1
    tail = "".join(current).strip()
    if tail:
        args.append(tail)
    return [arg for arg in args if arg]


TOKEN_RE = re.compile(r"\b[A-Z][A-Z0-9_]*\b")


def collect_terminals(
    productions: Dict[str, List[str]],
    known_tokens: Set[str],
    extra_tokens: Set[str],
) -> List[str]:
    used: Set[str] = set()
    for bodies in productions.values():
        for body in bodies:
            for candidate in TOKEN_RE.findall(body):
                if candidate in known_tokens or candidate in extra_tokens:
                    used.add(candidate)
    return sorted(used)


def render_ebnf(
    productions: Dict[str, List[str]],
    tokens: List[str],
    token_metadata: Dict[str, object],
    start: str,
) -> str:
    lines: List[str] = []
    lines.append("Line ::= tactic \".\"")
    lines.append("")

    for head in sorted(productions):
        if head == "Line":
            continue
        bodies = productions[head]
        lines.append(f"{head} ::= ")
        for idx, body in enumerate(bodies):
            prefix = "  | " if idx else "   "
            lines.append(f"{prefix}{body}")
        lines.append("")

    lines.append("Terminals:")
    for token in tokens:
        info = token_metadata.get(token)
        if not info:
            lines.append(f"  {token} ::= /* literal unknown */")
            continue
        literals = info.literals
        pattern = info.pattern
        if literals:
            joined = " | ".join(f"\"{lit}\"" for lit in literals)
            lines.append(f"  {token} ::= {joined}")
        elif pattern:
            lines.append(f"  {token} ::= /{pattern}/")
        else:
            lines.append(f"  {token} ::= /* literal unknown */")

    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    main()

