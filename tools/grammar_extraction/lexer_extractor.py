from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Set


@dataclass
class TokenInfo:
    """Represents textual spellings for a Menhir token."""

    name: str
    literals: Set[str] = field(default_factory=set)
    pattern: Optional[str] = None

    def merge_literals(self, values: Iterable[str]) -> None:
        self.literals.update(values)

    def as_dict(self) -> Dict[str, object]:
        payload: Dict[str, object] = {"name": self.name}
        if self.literals:
            payload["literals"] = sorted(self.literals)
        if self.pattern:
            payload["pattern"] = self.pattern
        return payload


@dataclass
class LexerInfo:
    """Lightweight container for all lexer-derived tokens."""

    tokens: Dict[str, TokenInfo]

    def ensure(self, name: str) -> TokenInfo:
        if name not in self.tokens:
            self.tokens[name] = TokenInfo(name=name)
        return self.tokens[name]

    def to_json(self) -> str:
        payload = {name: info.as_dict() for name, info in sorted(self.tokens.items())}
        return json.dumps(payload, indent=2, sort_keys=True)


KEYWORD_ENTRY_RE = re.compile(
    r'"(?P<literal>[^"]+)"\s*,\s*(?P<token>[A-Z][A-Z0-9_]*)', re.MULTILINE
)

LITERAL_RULE_RE = re.compile(
    r"\|\s*(?P<literal>(\"[^\"]+\")|('[^']+'))(?P<rest>.*?)\{\s*(?P<token>[A-Z][A-Z0-9_]*)",
    re.DOTALL,
)

OPERATOR_ENTRY_RE = re.compile(
    r'\("(?P<literal>[^"]+)"\s*,\s*\((?P<token>[A-Z][A-Z0-9_]*)',
    re.MULTILINE,
)


GENERIC_PATTERNS: Dict[str, str] = {
    "LIDENT": r"[a-z_][A-Za-z0-9_']*",
    "UIDENT": r"[A-Z][A-Za-z0-9_']*",
    "TIDENT": r"'?[A-Za-z][A-Za-z0-9_']*",
    "MIDENT": r"[A-Za-z0-9_.]+",
    "STRING": r'"([^"\\]|\\.)*"',
    "UINT": r"[0-9]+",
    "DECIMAL": r"[0-9]+\.[0-9]+",
}


def _strip_suffix_token(name: str) -> str:
    """Remove payload qualifiers such as `RING `Raw` → `RING`."""
    return name.strip().split()[0]


def _decode_literal(literal: str) -> str:
    if literal.startswith('"') and literal.endswith('"'):
        payload = literal[1:-1]
        try:
            return bytes(payload, "utf-8").decode("unicode_escape")
        except UnicodeDecodeError:
            return payload
    if literal.startswith("'") and literal.endswith("'"):
        value = literal[1:-1]
        if value.startswith("\\"):
            try:
                return bytes(value, "utf-8").decode("unicode_escape")
            except UnicodeDecodeError:
                return value
        return value
    return literal


def extract_lexer_info(path: Path) -> LexerInfo:
    text = path.read_text()
    tokens: Dict[str, TokenInfo] = {}
    info = LexerInfo(tokens=tokens)

    _populate_keyword_literals(text, info)
    _populate_operator_literals(text, info)
    _populate_literal_rules(text, info)
    _populate_generic_patterns(info)

    return info


def _populate_keyword_literals(source: str, info: LexerInfo) -> None:
    body = _extract_keyword_block(source)
    if not body:
        return
    for literal, token in KEYWORD_ENTRY_RE.findall(body):
        clean_token = _strip_suffix_token(token)
        info.ensure(clean_token).merge_literals([literal])


def _populate_literal_rules(source: str, info: LexerInfo) -> None:
    for match in LITERAL_RULE_RE.finditer(source):
        literal = match.group("literal")
        token = match.group("token")
        clean_token = _strip_suffix_token(token)
        info.ensure(clean_token).merge_literals([_decode_literal(literal)])


def _populate_operator_literals(source: str, info: LexerInfo) -> None:
    for literal, token in OPERATOR_ENTRY_RE.findall(source):
        clean_token = _strip_suffix_token(token)
        info.ensure(clean_token).merge_literals([_decode_literal(f'"{literal}"')])


def _populate_generic_patterns(info: LexerInfo) -> None:
    for name, pattern in GENERIC_PATTERNS.items():
        info.ensure(name).pattern = pattern


def _extract_keyword_block(source: str) -> str:
    marker = "let _keywords"
    start = source.find(marker)
    if start == -1:
        return ""
    start = source.find("[", start)
    if start == -1:
        return ""
    i = start + 1
    depth = 1
    in_string = False
    in_char = False
    escape = False
    body_chars: List[str] = []

    while i < len(source) and depth > 0:
        if source.startswith("(*", i):
            comment_depth = 1
            i += 2
            while comment_depth > 0 and i < len(source):
                if source.startswith("(*", i):
                    comment_depth += 1
                    i += 2
                elif source.startswith("*)", i):
                    comment_depth -= 1
                    i += 2
                else:
                    i += 1
            continue

        ch = source[i]
        if in_string:
            body_chars.append(ch)
            if ch == '"' and not escape:
                in_string = False
            escape = ch == "\\" and not escape
            i += 1
            continue
        if in_char:
            body_chars.append(ch)
            if ch == "'" and not escape:
                in_char = False
            escape = ch == "\\" and not escape
            i += 1
            continue

        if ch == '"':
            in_string = True
            body_chars.append(ch)
            i += 1
            continue
        if ch == "'":
            in_char = True
            body_chars.append(ch)
            i += 1
            continue
        if ch == "[":
            depth += 1
        elif ch == "]":
            depth -= 1
            if depth == 0:
                break
        body_chars.append(ch)
        i += 1

    return "".join(body_chars)


__all__ = ["LexerInfo", "TokenInfo", "extract_lexer_info"]

