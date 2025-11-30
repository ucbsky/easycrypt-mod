"""
Grammar extraction toolkit for EasyCrypt.

This package contains utilities to read the Menhir grammar/lexer definitions
and convert them into grammar representations that can be consumed by
grammar-constrained decoding backends (EBNF, PEG, JSON PEG, etc.).
"""

from .cfg_model import (
    Grammar,
    Nonterminal,
    Production,
    SymbolRef,
    Terminal,
)

__all__ = [
    "Grammar",
    "Nonterminal",
    "Production",
    "SymbolRef",
    "Terminal",
]

