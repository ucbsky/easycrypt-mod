from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Dict

from .lexer_extractor import extract_lexer_info
from .parser_extractor import ParserExtractionResult, extract_parser_info


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Extract a grammar from EasyCrypt's Menhir parser."
    )
    parser.add_argument(
        "--parser",
        type=Path,
        default=Path("src/ecParser.mly"),
        help="Path to ecParser.mly",
    )
    parser.add_argument(
        "--lexer",
        type=Path,
        default=Path("src/ecLexer.mll"),
        help="Path to ecLexer.mll",
    )
    parser.add_argument(
        "--dump-raw",
        type=Path,
        help="Optional JSON file to dump raw extraction results for debugging.",
    )
    return parser


def run() -> None:
    parser = build_arg_parser()
    args = parser.parse_args()

    lexer_info = extract_lexer_info(args.lexer)
    parser_info = extract_parser_info(args.parser)

    if args.dump_raw:
        payload: Dict[str, Any] = {
            "lexer": {name: info.as_dict() for name, info in lexer_info.tokens.items()},
            "parser": {
                "tokens": parser_info.tokens,
                "start_symbols": parser_info.start_symbols,
                "productions": [
                    {
                        "head": production.head,
                        "body": production.body,
                        "inline": production.inline,
                        "line": production.line,
                    }
                    for production in parser_info.productions
                ],
            },
        }
        args.dump_raw.parent.mkdir(parents=True, exist_ok=True)
        args.dump_raw.write_text(json.dumps(payload, indent=2))

    print(
        f"Extracted {len(parser_info.tokens)} parser tokens, "
        f"{len(parser_info.start_symbols)} start symbols, "
        f"{len(parser_info.productions)} productions, "
        f"{len(lexer_info.tokens)} lexer terminals."
    )


if __name__ == "__main__":
    run()

