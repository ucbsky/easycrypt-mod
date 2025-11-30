#!/usr/bin/env python3
"""
Quick helper script to inspect the size of the generated EasyCrypt grammar.

It prints high-level counts for the lexer and parser as well as a few expanded
productions so we can sanity-check specific non-terminals (e.g. `tactic`).
"""

from __future__ import annotations

import argparse
import json
import re
from collections import defaultdict, deque
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Set, Tuple


@dataclass
class Production:
    head: str
    body: List[str]
    raw: str


@dataclass
class SymbolChunk:
    symbol: str
    quantifier: str | None = None  # None, '?', '*', '+'


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Show basic statistics about the generated EasyCrypt grammar."
    )
    parser.add_argument(
        "--grammar-json",
        type=Path,
        default=Path(__file__).with_name("grammar_raw.json"),
        help="Path to the grammar JSON file (default: %(default)s).",
    )
    parser.add_argument(
        "--reduced-json",
        type=Path,
        default=Path(__file__).with_name("grammar_reduced.json"),
        help="Where to write the reduced grammar JSON (default: %(default)s).",
    )
    parser.add_argument(
        "--expr-collapsed-json",
        type=Path,
        default=Path(__file__).with_name("grammar_reduced_expr.json"),
        help="Where to write the expression-collapsed grammar JSON (default: %(default)s).",
    )
    parser.add_argument(
        "--expr-ebnf",
        type=Path,
        default=Path(__file__).with_name("grammar_reduced_expr.ebnf"),
        help="Where to write the expression-collapsed grammar in EBNF form.",
    )
    return parser.parse_args()


def load_grammar(json_path: Path) -> Dict[str, Any]:
    with json_path.open("r", encoding="utf-8") as f:
        return json.load(f)


def save_reduced_grammar(
    json_path: Path, reduced: Dict[str, List[Production]]
) -> None:
    def prod_to_dict(prod: Production) -> Dict[str, Any]:
        return {"body_symbols": prod.body, "raw_body": prod.raw}

    serializable: Dict[str, Any] = {}
    for head, prods in reduced.items():
        serializable[head] = [prod_to_dict(prod) for prod in prods]

    with json_path.open("w", encoding="utf-8") as f:
        json.dump(serializable, f, indent=2)


def write_ebnf(grammar: Dict[str, List[Production]], out_path: Path) -> None:
    heads = sorted(grammar.keys())
    lines: List[str] = []
    for head in heads:
        alts: List[str] = []
        for prod in grammar[head]:
            body = prod.body
            alts.append(" ".join(body) if body else "ε")
        rhs = " | ".join(alts)
        lines.append(f"{head} ::= {rhs}")
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


SYMBOL_PATTERN = re.compile(r"^[A-Za-z0-9_]+$")

WRAPPER_FUNCS = [
    "loc",
    "brace",
    "paren",
    "bracket",
    "prefix",
    "postfix",
    "seq",
    "either",
    "or3",
    "plist",
    "plist0",
    "plist1",
    "plist2",
    "plist3",
    "pseq",
    "list",
    "list0",
    "list1",
    "rlist",
    "rlist0",
    "rlist1",
    "rseq",
    "opt",
    "popt",
    "option",
    "poption",
    "repeat",
    "prepeat",
    "maybe",
    "pmaybe",
]


OPTIONAL_WRAPPERS = {
    "opt",
    "popt",
    "option",
    "poption",
    "boption",
    "iboption",
    "uoption",
    "maybe",
    "pmaybe",
}


LIST_PLUS_WRAPPERS = {
    "plist1",
    "plist2",
    "plist3",
    "list1",
    "rlist1",
    "plist",
    "list",
    "rlist",
    "pseq",
    "repeat",
    "prepeat",
}


LIST_STAR_WRAPPERS = {
    "plist0",
    "list0",
    "rlist0",
    "plist",
    "list",
    "rlist",
    "rseq",
}

LIST_RECURSIONS: Dict[str, Tuple[str, str]] = {
    # Allow arbitrarily long semicolon-separated tactic lists.
    "subtactics": ("subtactic", "SEMICOLON"),
}


def split_top_level_args(text: str) -> List[str]:
    args: List[str] = []
    depth = 0
    start = 0
    for idx, ch in enumerate(text):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        elif ch == "," and depth == 0:
            fragment = text[start:idx].strip()
            if fragment:
                args.append(fragment)
            start = idx + 1
    tail = text[start:].strip()
    if tail:
        args.append(tail)
    return args


ALIAS_HEADS: Dict[str, List[str]] = {
    # `outline_kind` holds the low-level program-manipulation tactics (proc, call,
    # inline, sim, ...). The Menhir grammar exposes them via the outline machinery,
    # but for line-by-line tactic parsing we need to treat them as regular tactics.
    "tactic_core_r": ["outline_kind"],
}


def strip_wrappers(body: str) -> str:
    def helper(text: str) -> str:
        result: List[str] = []
        i = 0
        length = len(text)
        while i < length:
            if text[i].isalpha() or text[i] == "_":
                j = i
                while j < length and (text[j].isalnum() or text[j] == "_"):
                    j += 1
                name = text[i:j]
                k = j
                while k < length and text[k].isspace():
                    k += 1
                if k < length and text[k] == "(" and name in WRAPPER_FUNCS:
                    depth = 1
                    k += 1
                    start = k
                    while k < length and depth > 0:
                        if text[k] == "(":
                            depth += 1
                        elif text[k] == ")":
                            depth -= 1
                        k += 1
                    raw_args = text[start : k - 1]
                    arg_segments = split_top_level_args(raw_args)
                    processed_args = [helper(arg) for arg in arg_segments if arg]
                    primary = processed_args[0] if processed_args else ""
                    combined = " ".join(fragment for fragment in processed_args if fragment)
                    if name in OPTIONAL_WRAPPERS:
                        result.append(primary + "?")
                    elif name in LIST_PLUS_WRAPPERS:
                        result.append(primary + "+")
                    elif name in LIST_STAR_WRAPPERS:
                        result.append(primary + "*")
                    else:
                        result.append(combined)
                    i = k
                    continue
                result.append(text[i:j])
                i = j
                continue
            result.append(text[i])
            i += 1
        return "".join(result)

    return helper(body)


def clean_symbol(symbol: str) -> str:
    cleaned = symbol.strip()
    cleaned = cleaned.strip(",(){}[]:")
    if "(" in cleaned:
        cleaned = cleaned.split("(", 1)[0]
    cleaned = cleaned.strip()
    while cleaned and cleaned[-1] in "+*?":
        cleaned = cleaned[:-1]
    cleaned = cleaned.replace("-", "_")
    replacements = {"|": "PIPE"}
    cleaned = replacements.get(cleaned, cleaned)
    if cleaned and not re.search(r"[A-Za-z0-9_]", cleaned):
        return ""
    return cleaned


def extract_quantifier(token: str) -> Tuple[str, str | None]:
    if not token:
        return token, None
    quant = None
    if token[-1] in "?*+":
        quant = token[-1]
        token = token[:-1]
    return token, quant


def tokenize_body(body: str) -> List[SymbolChunk]:
    """
    Turn a Menhir-style body string (like 'x=ident COLON ty=loc(type_exp)')
    into a list of grammar symbols: ['ident', 'COLON', 'type_exp'].
    """

    body_clean = strip_wrappers(body)

    body_clean = re.sub(r"\(P\)", "", body_clean)
    body_clean = re.sub(r"%prec\s+\S+", "", body_clean)
    body_clean = re.sub(r"%public", "", body_clean)
    body_clean = re.sub(r"/\*.*?\*/", " ", body_clean)
    body_clean = body_clean.replace(",", " ")

    tokens_raw = body_clean.split()
    symbols: List[SymbolChunk] = []
    for token in tokens_raw:
        if "=" in token:
            rhs = token.split("=")[-1]
            if rhs:
                base, quant = extract_quantifier(rhs)
                cleaned = clean_symbol(base)
                if cleaned:
                    symbols.append(SymbolChunk(symbol=cleaned, quantifier=quant))
        else:
            base, quant = extract_quantifier(token)
            cleaned = clean_symbol(base)
            if cleaned:
                symbols.append(SymbolChunk(symbol=cleaned, quantifier=quant))

    return symbols


def expand_symbol_chunks(chunks: List[SymbolChunk]) -> List[List[str]]:
    sequences: List[List[str]] = [[]]
    for chunk in chunks:
        symbol = chunk.symbol
        quant = chunk.quantifier
        if not symbol:
            continue
        if quant == "?":
            new_sequences: List[List[str]] = []
            for seq in sequences:
                new_sequences.append(seq.copy())
                new_sequences.append(seq + [symbol])
            sequences = new_sequences
        elif quant == "*":
            new_sequences = []
            for seq in sequences:
                new_sequences.append(seq.copy())
                new_sequences.append(seq + [symbol])
            sequences = new_sequences
        else:
            sequences = [seq + [symbol] for seq in sequences]
    return sequences


def summarize_productions(
    productions: List[Any],
) -> Tuple[Dict[str, List[Production]], Set[str], List[Production]]:
    head_to_prods: Dict[str, List[Production]] = defaultdict(list)
    all_heads: Set[str] = set()

    normalized_order: List[Production] = []

    for prod_data in productions:
        head = prod_data.get("head")
        body_str = prod_data.get("body", "")
        if not head:
            continue
        symbol_chunks = tokenize_body(body_str)
        expanded_bodies = expand_symbol_chunks(symbol_chunks)
        if not expanded_bodies:
            expanded_bodies = [[]]
        for body_syms in expanded_bodies:
            prod = Production(head=head, body=body_syms, raw=body_str)
            head_to_prods[head].append(prod)
            normalized_order.append(prod)
        all_heads.add(head)

    return head_to_prods, all_heads, normalized_order


def reachable_heads(
    seeds: List[str], head_to_prods: Dict[str, List[Production]], all_heads: Set[str]
) -> Set[str]:
    queue = deque([head for head in seeds if head in all_heads])
    visited: Set[str] = set(queue)

    while queue:
        head = queue.popleft()
        for prod in head_to_prods.get(head, []):
            for symbol in prod.body:
                if symbol in all_heads and symbol not in visited:
                    visited.add(symbol)
                    queue.append(symbol)

    return visited


def find_structure_heads(heads: Set[str]) -> List[str]:
    patterns = ["expr", "form", "sform", "form_r", "form_u", "pterm", "qident", "qoident"]
    extra = {
        "sexpr",
        "pcutdef",
        "pcutdef1",
        "fel_pred_spec",
        "fel_pred_specs",
        "gpterm",
        "gpterm_arg",
        "gpoterm",
        "gpoterm_head",
        "prod_form",
        "intro_pattern",
        "ipcore",
        "ipcore_name",
        "rwarg",
        "rwarg1",
        "rwpr_arg",
        "rwocc",
        "rwside",
        "rwrepeat",
        "im_stmt",
        "im_stmt_seq",
        "im_stmt_seq_r",
        "im_stmt_seq_named",
        "im_stmt_base",
        "im_stmt_base_r",
        "im_stmt_atomic",
        "inlineopt",
        "inlinepat",
        "inlinepat1",
        "inlinesubpat",
        "occurences",
        "smt_info",
        "smt_info1",
        "smt_option",
        "dbmap1",
        "dbmap_flag",
        "dbmap_target",
        "dbhint",
        "crushmode",
        "eqobs_in",
        "eqobs_in_pos",
        "eqobs_in_inv",
        "eqobs_in_eqpost",
        "eqobs_in_eqinv",
        "eqobs_in_eqglob1",
        "rnd_info",
        "semrndpos",
        "semrndpos1",
    }
    matches = [
        head for head in heads if any(pattern in head for pattern in patterns) or head in extra
    ]
    return sorted(matches)


def alias_productions(grammar: Dict[str, List[Production]]) -> None:
    for target, sources in ALIAS_HEADS.items():
        if target not in grammar:
            continue
        for src in sources:
            for prod in grammar.get(src, []):
                grammar[target].append(
                    Production(head=target, body=list(prod.body), raw=f"[alias:{src}] {prod.raw}")
                )
    if "tactic_core_r" in grammar:
        grammar["tactic_core_r"].append(
            Production(head="tactic_core_r", body=["RND"], raw="[synthetic] RND (no info)")
        )
        grammar["tactic_core_r"].append(
            Production(head="tactic_core_r", body=["SIM"], raw="[synthetic] SIM (no info)")
        )
        grammar["tactic_core_r"].append(
            Production(head="tactic_core_r", body=["MOVE", "EXPR"], raw="[synthetic] MOVE intro")
        )
        grammar["tactic_core_r"].append(
            Production(head="tactic_core_r", body=["RND", "EXPR"], raw="[synthetic] RND expr")
        )


def inject_list_recursions(grammar: Dict[str, List[Production]]) -> None:
    for head, (item, sep) in LIST_RECURSIONS.items():
        if head not in grammar:
            continue
        grammar[head].append(
            Production(
                head=head,
                body=[item, sep, head],
                raw=f"[synthetic:list] {head} -> {item} {sep} {head}",
            )
        )


def collapse_expression_heads(
    head_to_prods: Dict[str, List[Production]], expr_heads: Set[str]
) -> Dict[str, List[Production]]:
    collapsed: Dict[str, List[Production]] = {}
    for head, prods in head_to_prods.items():
        if head in expr_heads:
            continue
        new_prods: List[Production] = []
        for prod in prods:
            new_body = ["EXPR" if symbol in expr_heads else symbol for symbol in prod.body]
            new_prods.append(Production(head=head, body=new_body, raw=prod.raw))
        collapsed[head] = new_prods
    return collapsed


def add_line_start(grammar: Dict[str, List[Production]]) -> Dict[str, List[Production]]:
    if "Line" in grammar:
        raise ValueError("Grammar already defines a 'Line' head.")
    line_prods = [
        Production(head="Line", body=["tactic", "DOT"], raw="tactic DOT"),
        Production(head="Line", body=["tactics_or_prf", "DOT"], raw="tactics_or_prf DOT"),
        Production(head="Line", body=["stmt", "DOT"], raw="stmt DOT"),
        Production(head="Line", body=["stmt"], raw="stmt"),
        Production(head="Line", body=["QED", "DOT"], raw="QED DOT"),
    ]
    new_grammar: Dict[str, List[Production]] = {"Line": line_prods}
    new_grammar.update(grammar)
    return new_grammar


def validate_symbols(label: str, grammar: Dict[str, List[Production]]) -> None:
    invalid: List[Tuple[str, str, str]] = []
    for head, prods in grammar.items():
        for prod in prods:
            for symbol in prod.body:
                if not SYMBOL_PATTERN.fullmatch(symbol):
                    invalid.append((head, symbol, prod.raw))
                    if len(invalid) >= 10:
                        break
            if len(invalid) >= 10:
                break
        if len(invalid) >= 10:
            break
    if invalid:
        print(f"Found invalid symbols in {label}:")
        for head, symbol, raw in invalid:
            print(f"  head={head!r}, symbol={symbol!r}, raw={raw!r}")
        raise SystemExit(1)


def main() -> None:
    args = parse_args()
    ec = load_grammar(args.grammar_json)

    lexer: Dict[str, Any] = ec.get("lexer", {})
    parser_block: Dict[str, Any] = ec.get("parser", {})
    tokens = set(parser_block.get("tokens") or [])
    productions: List[Any] = parser_block.get("productions") or []

    print("Num lexer entries:", len(lexer))
    print("Num parser tokens:", len(tokens))
    print("Num productions:", len(productions))
    if productions:
        print("Sample production:", productions[0])
    else:
        print("Sample production: <none available>")

    head_to_prods, all_heads, normalized = summarize_productions(productions)
    print("Num heads:", len(all_heads))
    print("Num normalized productions:", len(normalized))
    sample_normalized = normalized[:5]
    if sample_normalized:
        print("Sample normalized productions:")
        for prod in sample_normalized:
            print(f"  head={prod.head!r}")
            print(f"    body_symbols={prod.body}")
            print(f"    raw_body={prod.raw!r}")
    else:
        print("Sample normalized productions: <none available>")

    focused_heads = ["tactic", "tactic_ip", "tactic_core"]
    for head in focused_heads:
        prods = head_to_prods.get(head, [])
        if not prods:
            print(f"No productions found for '{head}'.")
            continue
        print(f"Productions for '{head}' ({len(prods)} total):")
        for prod in prods:
            print(f"  body_symbols={prod.body}")
            print(f"    raw_body={prod.raw!r}")

    seed_heads = sorted(
        {
            "tactic",
            "tactic_ip",
            "tactic_core",
            "tactic_core_r",
            "tactic_chain",
            "tactic_chain_r",
            "tactic_genip",
            "logtactic",
            "phltactic",
            "tactics",
            "tactics0",
            "toptactic",
            "tactics_or_prf",
            "tcd_toptactic",
            "tactic_dump",
            "outline_kind",
            "eager_tac",
            "stmt",
            "instr",
            "block",
            "base_instr",
            "proof",
            "proofend",
            "script",
            "command",
            "proc_decl",
            "qed",
            "call",
            "rnd",
            "inline",
            "rewrite",
            "byequiv",
            "move",
            "sim",
            "auto",
            "trivial",
            "field",
            "smt",
            "assert",
            "while",
            "match",
            "if",
            "have",
            "pose",
            "wlog",
            "apply",
            "change",
            "subst",
            "elim",
            "left",
            "right",
            "exist",
            "congr",
            "split",
            "alg_norm",
            "by",
            "do",
            "case",
            "progress",
            "rweqv_proc",
            "rweqv_res",
            "trans_hyp",
            "trans_kind",
            "repl_hyp",
            "repl_kind",
            "bdhoare_split",
            "async_while_tac_info",
            "while_tac_info",
            "semrndpos",
            "semrndpos1",
            "rnd_info",
            "interleave_info",
            "app_bd_info",
            "if_option",
            "eqobs_in",
            "eqobs_in_pos",
            "eqobs_in_inv",
            "eqobs_in_eqinv",
            "eqobs_in_eqglob1",
            "eqobs_in_eqpost",
            "fel_pred_spec",
            "fel_pred_specs",
            "cqoption",
            "cqoptionkw",
            "cqoptions",
            "typed_vars_or_anons",
            "var_or_anon",
            "param_decl",
            "ID",
        }
    )
    reachable = reachable_heads(seed_heads, head_to_prods, all_heads)
    print(f"Reachable heads from seeds ({len(reachable)} total):")
    for head in sorted(reachable):
        print(f"  - {head}")

    reduced_head_to_prods = {head: head_to_prods[head] for head in reachable}
    alias_productions(reduced_head_to_prods)
    inject_list_recursions(reduced_head_to_prods)
    reduced_prod_count = sum(len(prods) for prods in reduced_head_to_prods.values())
    print(f"Reduced grammar production count: {reduced_prod_count}")
    first_heads = sorted(reduced_head_to_prods.keys())[:20]
    print("First 20 heads alphabetically in reduced grammar:")
    for head in first_heads:
        print(f"  - {head}")
    reduced_with_line = add_line_start(reduced_head_to_prods)
    validate_symbols("reduced grammar", reduced_with_line)
    save_reduced_grammar(args.reduced_json, reduced_with_line)
    print(f"Reduced grammar written to: {args.reduced_json}")

    struct_heads = find_structure_heads(set(reduced_head_to_prods.keys()))
    print("Candidate expression/form heads to collapse:")
    for head in struct_heads:
        print(f"  - {head}")

    expr_head_set = set(struct_heads)
    collapsed_head_to_prods = collapse_expression_heads(reduced_head_to_prods, expr_head_set)
    collapsed_prod_count = sum(len(prods) for prods in collapsed_head_to_prods.values())
    collapsed_with_line = add_line_start(collapsed_head_to_prods)
    validate_symbols("expression-collapsed grammar", collapsed_with_line)
    save_reduced_grammar(args.expr_collapsed_json, collapsed_with_line)
    print(
        f"Expression-collapsed grammar written to: {args.expr_collapsed_json} "
        f"({collapsed_prod_count} productions)"
    )
    write_ebnf(collapsed_with_line, args.expr_ebnf)
    print(f"Expression-collapsed EBNF written to: {args.expr_ebnf}")

    sample_collapsed: List[Production] = []
    expr_sample: Production | None = None
    for head in sorted(collapsed_head_to_prods.keys()):
        prods = collapsed_head_to_prods[head]
        if not prods:
            continue
        sample_collapsed.append(Production(head=head, body=prods[0].body, raw=prods[0].raw))
        if not expr_sample:
            for prod in prods:
                if "EXPR" in prod.body:
                    expr_sample = Production(head=head, body=prod.body, raw=prod.raw)
                    break
        if len(sample_collapsed) >= 5:
            break
    if not expr_sample:
        for head, prods in collapsed_head_to_prods.items():
            for prod in prods:
                if "EXPR" in prod.body:
                    expr_sample = Production(head=head, body=prod.body, raw=prod.raw)
                    break
            if expr_sample:
                break
    if sample_collapsed:
        print("Sample productions from expression-collapsed grammar:")
        for prod in sample_collapsed:
            print(f"  head={prod.head!r}, body_symbols={prod.body}")
        if expr_sample:
            print(
                f"  (with EXPR) head={expr_sample.head!r}, "
                f"body_symbols={expr_sample.body}"
            )
    else:
        print("No productions available in expression-collapsed grammar.")


if __name__ == "__main__":
    main()

