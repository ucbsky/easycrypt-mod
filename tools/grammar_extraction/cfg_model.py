from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple


@dataclass(frozen=True)
class Terminal:
    """Represents a Menhir token / terminal symbol."""

    name: str
    literals: Tuple[str, ...] = ()
    pattern: Optional[str] = None

    @staticmethod
    def from_literals(name: str, literals: Iterable[str]) -> "Terminal":
        literals_tuple = tuple(dict.fromkeys(literals))  # preserve order
        return Terminal(name=name, literals=literals_tuple)


@dataclass(frozen=True)
class SymbolRef:
    """Reference to either a terminal or a nonterminal in a production body."""

    name: str
    kind: str  # "terminal" | "nonterminal"

    def __post_init__(self) -> None:
        if self.kind not in {"terminal", "nonterminal"}:
            raise ValueError(f"Invalid symbol kind {self.kind!r} for {self.name}")

    @property
    def is_terminal(self) -> bool:
        return self.kind == "terminal"


@dataclass
class Production:
    """One production rule head -> body."""

    head: str
    body: List[SymbolRef] = field(default_factory=list)
    guard: Optional[str] = None  # For later extensions (e.g., precedence hints)

    def body_as_names(self) -> List[str]:
        return [symbol.name for symbol in self.body]


@dataclass
class Nonterminal:
    """A nonterminal symbol with its productions."""

    name: str
    productions: List[Production] = field(default_factory=list)
    metadata: Dict[str, str] = field(default_factory=dict)

    def add_production(self, production: Production) -> None:
        if production.head != self.name:
            raise ValueError(
                f"Production head {production.head} does not match {self.name}"
            )
        self.productions.append(production)


@dataclass
class Grammar:
    """Complete grammar representation that can be exported to various formats."""

    start_symbols: List[str]
    terminals: Dict[str, Terminal] = field(default_factory=dict)
    nonterminals: Dict[str, Nonterminal] = field(default_factory=dict)

    def ensure_nonterminal(self, name: str) -> Nonterminal:
        if name not in self.nonterminals:
            self.nonterminals[name] = Nonterminal(name=name)
        return self.nonterminals[name]

    def add_production(self, head: str, body: Sequence[SymbolRef]) -> None:
        nt = self.ensure_nonterminal(head)
        nt.add_production(Production(head=head, body=list(body)))

    def add_terminal(self, terminal: Terminal) -> None:
        self.terminals[terminal.name] = terminal

    def referenced_symbols(self) -> Set[str]:
        refs: Set[str] = set()
        for nt in self.nonterminals.values():
            refs.add(nt.name)
            for production in nt.productions:
                refs.update(production.body_as_names())
        return refs

