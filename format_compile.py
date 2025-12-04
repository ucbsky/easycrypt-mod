#!/usr/bin/env python3
"""
Wrapper around `easycrypt compile` that regenerates proof scripts.

Usage:
    python format_compile.py [easycrypt compile flags] <file.ec>

Steps:
1. Run `easycrypt compile` with --dump-proof-ast (and -no-eco unless already set).
2. Feed the resulting <file>.proofast.json to the local `formatter` script.
3. Compile the formatted file (<file>.formatted.ec) with the same flags (no
   extra dump flag).
"""
from __future__ import annotations

import shutil
import subprocess
import sys
from pathlib import Path
from typing import List


def usage() -> None:
    print(__doc__.strip())


def contains_flag(flags: List[str], *names: str) -> bool:
    return any(flag in names for flag in flags)


def with_common_flags(flags: List[str], add_dump: bool) -> List[str]:
    prefix: List[str] = []
    if add_dump and not contains_flag(flags, "-dump-proof-ast", "--dump-proof-ast"):
        prefix.append("-dump-proof-ast")
    if not contains_flag(flags, "-no-eco", "--no-eco"):
        prefix.append("-no-eco")
    return prefix + list(flags)


def run_cmd(args: List[str]) -> None:
    print("+", " ".join(args))
    subprocess.run(args, check=True)


def easycrypt_command() -> List[str]:
    dune = shutil.which("dune")
    if dune:
        return [dune, "exec", "easycrypt", "--"]
    binary = shutil.which("easycrypt")
    if not binary:
        raise FileNotFoundError("unable to locate 'easycrypt' binary or 'dune'")
    return [binary]


def main(argv: List[str]) -> int:
    if len(argv) < 2:
        usage()
        return 1

    flags = argv[1:-1]
    target = Path(argv[-1]).resolve()

    if not target.exists():
        print(f"error: input file '{target}' does not exist", file=sys.stderr)
        return 1

    try:
        ec_cmd = easycrypt_command()
    except FileNotFoundError as err:
        print(f"error: {err}", file=sys.stderr)
        return 1

    formatter = Path(__file__).resolve().parent / "formatter.py"
    if not formatter.exists():
        print(f"error: formatter script not found at '{formatter}'", file=sys.stderr)
        return 1

    # Phase 1: compile original file with proof AST dump.
    compile_flags = with_common_flags(flags, add_dump=True)
    cmd = [*ec_cmd, "compile", *compile_flags, str(target)]
    run_cmd(cmd)

    json_path = target.with_suffix(".proofast.json")
    if not json_path.exists():
        print(f"error: proof AST '{json_path}' was not produced", file=sys.stderr)
        return 1

    # Run formatter.
    run_cmd([str(formatter), str(target), str(json_path)])

    suffix = target.suffix
    base = target.with_suffix("")
    formatted = Path(f"{base}.formatted{suffix}")
    if not formatted.exists():
        print(f"error: formatted file '{formatted}' was not created", file=sys.stderr)
        return 1

    # Phase 2: compile formatted file.
    compile_formatted_flags = with_common_flags(flags, add_dump=False)
    cmd = [*ec_cmd, "compile", *compile_formatted_flags, str(formatted)]
    run_cmd(cmd)

    print(f"Formatted file compiled successfully: {formatted}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))

