from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional


@dataclass
class RawProduction:
    head: str
    body: str
    inline: bool
    line: int


@dataclass
class ParserExtractionResult:
    tokens: List[str]
    start_symbols: List[str]
    productions: List[RawProduction]


TOKEN_DECL_RE = re.compile(r"^%token(?P<payload>\s+<[^>]+>)?\s+(?P<body>.*)$")
START_DECL_RE = re.compile(r"^%start\s+(?P<body>.*)$")
NT_DECL_RE = re.compile(
    r"^(%inline\s+)?(?P<name>[\w']+(?:\([^)]*\))?)\s*:(?P<body>.*)$"
)
ALT_DECL_RE = re.compile(r"^\|\s*(?P<body>.*)$")


def extract_parser_info(path: Path) -> ParserExtractionResult:
    text = path.read_text()
    header, grammar = _split_sections(text)

    tokens = _parse_token_decls(header)
    starts = _parse_start_decls(header)
    raw_productions = _parse_grammar(grammar)

    return ParserExtractionResult(tokens=tokens, start_symbols=starts, productions=raw_productions)


def _split_sections(text: str) -> tuple[str, str]:
    marker = "%%"
    if marker not in text:
        raise ValueError("Menhir file is missing %% separator")
    before, after = text.split(marker, 1)
    return before, after


def _strip_inline_comment(line: str) -> str:
    if "(*" not in line:
        return line
    result = []
    depth = 0
    i = 0
    while i < len(line):
        if line.startswith("(*", i):
            depth += 1
            i += 2
            while depth > 0 and i < len(line):
                if line.startswith("(*", i):
                    depth += 1
                    i += 2
                elif line.startswith("*)", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            continue
        result.append(line[i])
        i += 1
    return "".join(result)


def _parse_token_decls(header: str) -> List[str]:
    tokens: List[str] = []
    for raw_line in header.splitlines():
        line = raw_line.strip()
        if not line:
            continue
        m = TOKEN_DECL_RE.match(_strip_inline_comment(line))
        if not m:
            continue
        body = m.group("body").strip()
        body = re.sub(r"<[^>]+>", "", body).strip()
        for token in re.split(r"\s+", body):
            if token:
                tokens.append(token)
    return tokens


def _parse_start_decls(header: str) -> List[str]:
    starts: List[str] = []
    for raw_line in header.splitlines():
        line = raw_line.strip()
        if not line:
            continue
        m = START_DECL_RE.match(_strip_inline_comment(line))
        if not m:
            continue
        body = m.group("body").strip()
        for symbol in re.split(r"\s+", body):
            if symbol:
                starts.append(symbol)
    return starts


def _strip_ocaml_actions(grammar: str) -> str:
    result = []
    i = 0
    depth = 0
    while i < len(grammar):
        if grammar.startswith("(*", i):
            depth_comment = 1
            i += 2
            while depth_comment > 0 and i < len(grammar):
                if grammar.startswith("(*", i):
                    depth_comment += 1
                    i += 2
                elif grammar.startswith("*)", i):
                    depth_comment -= 1
                    i += 2
                else:
                    i += 1
            continue
        char = grammar[i]
        if char == "{":
            brace_depth = 1
            i += 1
            while brace_depth > 0 and i < len(grammar):
                if grammar.startswith("(*", i):
                    depth_comment = 1
                    i += 2
                    while depth_comment > 0 and i < len(grammar):
                        if grammar.startswith("(*", i):
                            depth_comment += 1
                            i += 2
                        elif grammar.startswith("*)", i):
                            depth_comment -= 1
                            i += 2
                        else:
                            i += 1
                    continue
                elif grammar[i] == "{":
                    brace_depth += 1
                elif grammar[i] == "}":
                    brace_depth -= 1
                    if brace_depth == 0:
                        i += 1
                        break
                i += 1
            result.append(" ")
            continue
        result.append(char)
        i += 1
    return "".join(result)


def _parse_grammar(grammar_text: str) -> List[RawProduction]:
    stripped = _strip_ocaml_actions(grammar_text)
    productions: List[RawProduction] = []
    current_head: Optional[str] = None
    current_inline = False
    buffer: Optional[str] = None
    current_line = 0

    lines = stripped.splitlines()
    for idx, raw_line in enumerate(lines):
        line = raw_line.rstrip()
        current_line = idx + 1
        if not line.strip():
            continue

        nt_match = NT_DECL_RE.match(line.strip())
        if nt_match:
            if buffer is not None and current_head:
                productions.append(
                    RawProduction(
                        head=current_head,
                        body=buffer.strip(),
                        inline=current_inline,
                        line=current_line,
                    )
                )
                buffer = None
            raw_name = nt_match.group("name")
            current_head = raw_name.split("(", 1)[0]
            current_inline = bool(nt_match.group(1))
            rest = nt_match.group("body").strip()
            if rest:
                buffer = rest
            else:
                buffer = None
            continue

        if current_head is None:
            continue

        alt_match = ALT_DECL_RE.match(line)
        if alt_match:
            if buffer is not None:
                productions.append(
                    RawProduction(
                        head=current_head,
                        body=buffer.strip(),
                        inline=current_inline,
                        line=current_line,
                    )
                )
            buffer = alt_match.group("body").strip()
            continue

        if buffer is None:
            buffer = line.strip()
        else:
            buffer = f"{buffer} {line.strip()}"

    if buffer is not None and current_head:
        productions.append(
            RawProduction(
                head=current_head,
                body=buffer.strip(),
                inline=current_inline,
                line=current_line,
            )
        )

    return [prod for prod in productions if prod.body]


__all__ = ["ParserExtractionResult", "RawProduction", "extract_parser_info"]

