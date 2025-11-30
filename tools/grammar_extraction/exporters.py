from __future__ import annotations

import json
from pathlib import Path
from typing import Iterable, List

from .cfg_model import Grammar, Production, SymbolRef


def grammar_to_ebnf(grammar: Grammar) -> str:
    """Render the internal grammar to a simple EBNF-like format."""

    lines: List[str] = []
    for start in grammar.start_symbols:
        lines.append(f"# start: {start}")

    for name in sorted(grammar.nonterminals):
        nonterminal = grammar.nonterminals[name]
        lines.append(f"{nonterminal.name} ::=")
        for production in nonterminal.productions:
            body = " ".join(_format_symbol(symbol) for symbol in production.body)
            lines.append(f"  | {body or '/* empty */'}")
        lines.append("")
    return "\n".join(lines).strip() + "\n"


def grammar_to_json(grammar: Grammar) -> str:
    payload = {
        "start": grammar.start_symbols,
        "rules": {
            name: [
                [symbol.name for symbol in production.body]
                for production in nonterminal.productions
            ]
            for name, nonterminal in sorted(grammar.nonterminals.items())
        },
        "terminals": {
            name: {
                "literals": list(terminal.literals),
                **({"pattern": terminal.pattern} if terminal.pattern else {}),
            }
            for name, terminal in sorted(grammar.terminals.items())
        },
    }
    return json.dumps(payload, indent=2, sort_keys=True)


def write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content)


def _format_symbol(symbol: SymbolRef) -> str:
    if symbol.is_terminal:
        return f"'{symbol.name}'"
    return symbol.name


__all__ = ["grammar_to_ebnf", "grammar_to_json", "write_text"]

