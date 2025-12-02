#!/usr/bin/env python3
"""
Parse an EasyCrypt file (.ec) and extract:
- Import headers as comma-separated list
- Lemmas with their statements and proofs
- Other intermediate content

Outputs a JSON file with all content in sequential order.
Comments (* *) are removed from all content.
"""

import re
import json
import sys
from pathlib import Path


def remove_comments(text: str) -> str:
    """
    Remove all EasyCrypt comments of the form (* ... *), including nested and
    multi-line comments, using a simple stack-based scanner.

    We completely remove the comment delimiters and their contents. Newlines
    that occur inside comments are dropped (matching the previous behavior
    where multi-line comments collapsed into surrounding text).
    """
    out: list[str] = []
    i = 0
    n = len(text)
    depth = 0

    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""

        if depth == 0:
            # Look for the start of a comment.
            if ch == "(" and nxt == "*":
                depth = 1
                i += 2
                continue
            else:
                out.append(ch)
                i += 1
        else:
            # Inside a comment; support nesting.
            if ch == "(" and nxt == "*":
                depth += 1
                i += 2
                continue
            if ch == "*" and nxt == ")":
                depth -= 1
                i += 2
                continue
            # Skip all other characters inside comments.
            i += 1

    return "".join(out)


def extract_imports_and_clones(text):
    """
    Extract module names from require import, require, clone, clone import, and import statements.
    Scans the ENTIRE text, not just headers, to catch imports throughout the file.
    Returns deduplicated list of imported/cloned module names (preserves first occurrence order).
    """
    imports = []
    seen = set()
    
    for line in text.split('\n'):
        line_stripped = line.strip()
        if not line_stripped:
            continue
        
        # Pattern 1: require [export] import Module1 Module2 ... .
        # Extracts: Module1, Module2, ...
        if line_stripped.startswith('require') and 'import' in line_stripped:
            match = re.match(r'require\s+(?:export\s+)?import\s+([^.]+)\.', line_stripped)
            if match:
                modules = match.group(1).strip().split()
                for mod in modules:
                    if mod not in seen:
                        imports.append(mod)
                        seen.add(mod)
        
        # Pattern 2: require (****) Module1 Module2 ... .
        # Extracts: all module names after an optional inline comment, but only
        # when there is no 'import' keyword (handled by pattern 1).
        elif line_stripped.startswith('require'):
            match = re.match(r'require\s+(?:\([^)]*\)\s+)?([^.]+)\.', line_stripped)
            if match:
                modules = match.group(1).strip().split()
                for mod in modules:
                    if mod not in seen:
                        imports.append(mod)
                        seen.add(mod)
        
        # Pattern 3: clone import ModulePath with ... (can span multiple lines, we get the module)
        # Extracts: ModulePath
        elif line_stripped.startswith('clone') and 'import' in line_stripped:
            match = re.match(r'clone\s+import\s+([\w.]+)', line_stripped)
            if match:
                mod = match.group(1)
                if mod not in seen:
                    imports.append(mod)
                    seen.add(mod)

        # Pattern 4: clone [include] ModulePath as Alias.
        # Extracts: ModulePath (before 'as' / 'with')
        # Handles both:
        #   clone ModulePath as M.
        #   clone include GenericSigmaProtocol with ...
        elif line_stripped.startswith('clone'):
            match = re.match(r'clone\s+(?:include\s+)?([\w.]+)(?:\s+as\s+\w+)?', line_stripped)
            if match:
                mod = match.group(1)
                if mod not in seen:
                    imports.append(mod)
                    seen.add(mod)
        
        # Pattern 5: import Module1 Module2 ... .
        # Standalone import statement (not preceded by require/clone)
        # Extracts: Module1, Module2, ...
        elif line_stripped.startswith('import'):
            match = re.match(r'import\s+([^.]+)\.', line_stripped)
            if match:
                modules = match.group(1).strip().split()
                for mod in modules:
                    if mod not in seen:
                        imports.append(mod)
                        seen.add(mod)
    
    return imports


def normalize_proof_body(proof_body: str) -> str:
    """
    Normalize proof body so that each tactic (ending with '.') is on its own line.

    Heuristic:
    - A tactic boundary is a '.' where the next character is whitespace or end-of-string.
    - We DO NOT split on dots that are followed by an identifier character, so names like
      'FMap.x' are preserved.
    """
    body = proof_body.strip()
    if not body:
        return body

    chunks = []
    current = []
    i = 0
    n = len(body)

    while i < n:
        ch = body[i]
        current.append(ch)

        if ch == ".":
            next_ch = body[i + 1] if i + 1 < n else ""
            # End of tactic: dot followed by whitespace or end-of-string
            if i + 1 == n or next_ch.isspace():
                # Emit current chunk as a line
                line = "".join(current).strip()
                if line:
                    chunks.append(line)
                # Skip following whitespace
                i += 1
                while i < n and body[i].isspace():
                    i += 1
                current = []
                continue

        i += 1

    # Remaining tail (if any)
    tail = "".join(current).strip()
    if tail:
        chunks.append(tail)

    return "\n".join(chunks)


def parse_easycrypt_file(file_path):
    """Parse an EasyCrypt file and extract structured content."""
    with open(file_path, 'r') as f:
        content = f.read()
    
    # Remove all comments first
    content = remove_comments(content)
    
    result = {
        "source_file": str(file_path),
        # Filled below: 'imports' for all imported modules,
        # 'local_imports' optionally used by repo-level tools.
        "imports": [],
        "local_imports": [],
        "content": [],
    }
    
    lines = content.split('\n')
    
    # Extract imports from the ENTIRE file (they can appear anywhere, not just at the top)
    # At this stage we don't know which ones are local vs stdlib; repo-level
    # tools (parse_repo) will reclassify into imports/local_imports.
    result["imports"] = extract_imports_and_clones(content)
    
    # Collect initial header lines for structure preservation
    # These appear at the top before any content definitions
    header_section = []
    i = 0
    while i < len(lines):
        line = lines[i].strip()
        # Header keywords: require, clone (with instantiations), import, prover, pragma
        # Stop when we see: axiom, section, declare, op, type, module, theory, etc.
        if (line.startswith('require') or 
            line.startswith('clone') or
            line.startswith('import') or
            line.startswith('prover') or
            line == ''):
            header_section.append(lines[i])
            i += 1
        else:
            # Stop header collection when we hit content
            break
    
    # Store ALL header content (including imports) as "other" type
    header_content = [line for line in header_section if line.strip()]
    if header_content:
        result["content"].append({
            "type": "other",
            "content": '\n'.join(header_content)
        })
    
    # Now parse the rest for axioms, lemmas, and other content
    remaining_content = '\n'.join(lines[i:])
    
    pos = 0
    
    while pos < len(remaining_content):
        # Look for axiom, lemma, or local lemma at start of a line
        # Pattern: match 'axiom', 'lemma', or 'local lemma', or 'equiv', or 'local equiv' followed by identifier
        item_match = re.search(
            r'(?:^|\n)\s*(axiom|(?:local\s+)?lemma|(?:local\s+)?equiv|(?:local\s+)?hoare)\s+(\w+)',
            remaining_content[pos:],
            re.MULTILINE
        )
        
        if not item_match:
            # No more axioms/lemmas, add rest as "other"
            rest = remaining_content[pos:].strip()
            if rest:
                result["content"].append({
                    "type": "other",
                    "content": rest
                })
            break
        
        # Add content before axiom/lemma as "other"
        before = remaining_content[pos:pos + item_match.start()].strip()
        if before:
            result["content"].append({
                "type": "other",
                "content": before
            })
        
        item_start = pos + item_match.start()
        item_type = item_match.group(1)  # 'axiom' or 'lemma' or 'local lemma'
        item_name = item_match.group(2)
        
        # Detect inline instantiations inside clone/import blocks such as
        # "lemma Foo <- Bar," (no statement/proof, often comma-terminated).
        # Treat these as non-definitions and keep the raw text in "other".
        line_start = item_start
        while line_start < len(remaining_content) and remaining_content[line_start] in "\r\n":
            line_start += 1
        line_end = remaining_content.find('\n', line_start)
        if line_end == -1:
            line_end = len(remaining_content)
        first_line = remaining_content[line_start:line_end]
        colon_idx = first_line.find(':')
        arrow_idx = first_line.find('<-')
        inline_instantiation = (
            arrow_idx != -1 and (colon_idx == -1 or arrow_idx < colon_idx)
        )

        if inline_instantiation:
            inst_end = line_end + 1 if line_end < len(remaining_content) else line_end
            instantiation = remaining_content[item_start:inst_end].rstrip()
            result["content"].append({
                "type": "other",
                "content": instantiation
            })
            pos = inst_end
            continue

        # Check if this is a lemma/axiom instantiation (has '<-')
        # Example: "lemma prime_order <- prime_p." or "axiom foo <- bar."
        # These are NOT actual definitions, skip them
        # Look ahead to find the full statement (up to the first '.')
        dot_pos = remaining_content.find('.', item_start)
        if dot_pos == -1:
            raise ValueError(f"ERROR: {item_type} '{item_name}' has no terminating '.'")
        statement_preview = remaining_content[item_start:dot_pos+1]
        
        if '<-' in statement_preview:
            # This is an instantiation, not a definition - skip it as "other"
            end_pos = dot_pos + 1
            instantiation = remaining_content[item_start:end_pos].strip()
            result["content"].append({
                "type": "other",
                "content": instantiation
            })
            pos = end_pos
            continue
        
        # Is this an axiom or a lemma?
        is_axiom = item_type == 'axiom'
        
        if is_axiom:
            # Axioms have no proof - just find the statement ending with '.'.
            # Heuristic (choose the earliest plausible terminator):
            #   - '.' at end-of-line (not preceded by another '.')
            #   - '.' followed by whitespace (not preceded by another '.')
            segment = remaining_content[item_start:]
            m1 = re.search(r'(?<!\.)\.\s*(?:\n|$)', segment)
            m2 = re.search(r'(?<!\.)\.(?=\s)', segment)
            candidates = [m for m in (m1, m2) if m]
            if not candidates:
                raise ValueError(
                    f"ERROR: Axiom '{item_name}' statement does not end with '.'\n"
                    f"Expected format: axiom <name> : <statement>."
                )
            stmt_rel = min(candidates, key=lambda m: m.start())
            stmt_end = item_start + stmt_rel.end()
            statement = remaining_content[item_start:stmt_end].strip()
            
            result["content"].append({
                "type": "axiom",
                "name": item_name,
                "statement": statement
            })
            pos = stmt_end
            
        else:
            # This is a lemma - find statement and proof.
            # Supported shapes:
            # 1. "lemma <name> : <statement>.\nproof.\n<tactics>\nqed."
            # 2. "lemma <name> : <statement>.\n<tactics>\nqed."   (implicit proof)
            # 3. "lemma <name> : <statement> by tactic."          (inline 'by' lemma)

            # Generic lemma with explicit or implicit proof.
            #
            # Step 1: find the end of the lemma statement.
            # Heuristic (choose the earliest plausible terminator):
            #   - '.' at end-of-line (followed by whitespace/newline/EOF),
            #     not preceded by another '.'
            #   - '.' followed by whitespace (not preceded by '.')
            # This handles both forms:
            #   lemma name ... .\nproof.\n...
            #   lemma name ... . smt(). qed.
            segment = remaining_content[item_start:]
            m1 = re.search(r'(?<!\.)\.\s*(?:\n|$)', segment)
            m2 = re.search(r'(?<!\.)\.(?=\s)', segment)
            candidates = [m for m in (m1, m2) if m]
            if not candidates:
                raise ValueError(
                    f"ERROR: Lemma '{item_name}' statement does not end with '.'\n"
                    f"Expected format: lemma <name> : <statement>."
                )
            stmt_rel = min(candidates, key=lambda m: m.start())
            
            stmt_end = item_start + stmt_rel.end()
            statement = remaining_content[item_start:stmt_end].strip()

            # Special case: inline "by" lemma, e.g.:
            #   lemma name ... = ... by tactic.
            # Here everything before " by " is the statement, and "by ..." is
            # the whole proof (we wrap it in proof./qed.).
            # Detect a 'by' keyword anywhere in the statement (possibly on the
            # next line), surrounded by whitespace:
            #   lemma name ... = ...\nby tactic.
            m_by = re.search(r'\sby\s', statement)
            if m_by:
                by_start, by_end = m_by.span()
                stmt_text = statement[:by_start].rstrip()
                proof_tail = statement[by_end:].strip()

                if not stmt_text.endswith('.'):
                    stmt_text = stmt_text + '.'

                if not proof_tail.endswith('.'):
                    proof_tail = proof_tail + '.'

                proof_body = f"by {proof_tail}".strip()
                proof_body = normalize_proof_body(proof_body)

                # Count tactics: number of non-empty lines ending with '.'
                tactic_count = sum(
                    1 for ln in proof_body.split("\n")
                    if ln.strip() and ln.strip().endswith('.')
                )

                # Sanity check: proof must not be empty and must not contain
                # nested declarations (lemma, axiom, etc.).
                if tactic_count == 0:
                    raise ValueError(
                        f"ERROR: Lemma '{item_name}' has empty proof body after 'by'.\n"
                        f"Expected at least one tactic after 'by'."
                    )

                FORBIDDEN_KEYWORDS = [
                    'proof.', 'qed.', 'lemma ', 'local lemma', 'axiom ',
                    'op ', 'type ', 'module ', 'theory ', 'section ',
                    'end section', 'require ', 'clone '
                ]
                for line in proof_body.split('\n'):
                    stripped = line.strip()
                    for keyword in FORBIDDEN_KEYWORDS:
                        if stripped.startswith(keyword):
                            raise ValueError(
                                f"ERROR: Lemma '{item_name}' has forbidden keyword '{keyword}' in proof.\n"
                                f"This indicates nested proofs or parsing error.\n"
                                f"Line: {stripped[:100]}"
                            )

                result["content"].append({
                    "type": "lemma",
                    "name": item_name,
                    "statement": stmt_text,
                    "proof": f"proof.\n{proof_body}\nqed.",
                    "tactics": tactic_count,
                })
                pos = stmt_end
                continue

            tail = remaining_content[stmt_end:]
            qed_search = re.search(r'\bqed\s*\.', tail)
            
            if not qed_search:
                # No qed found after the lemma statement – this means we cannot
                # determine a well-formed proof region for this lemma.
                raise ValueError(
                    f"ERROR: Lemma '{item_name}' has no terminating 'qed.' after its statement.\n"
                    f"Expected format: {item_type} <name> : <statement>. [proof.] <tactics> qed."
                )
            
            # qed exists - extract the proof (bounded by this tail)
            qed_pos = stmt_end + qed_search.end()
            proof_content_raw = remaining_content[stmt_end:qed_pos].strip()
            
            # Check if proof starts with 'proof.' keyword
            has_explicit_proof = proof_content_raw.startswith('proof.')
            
            if has_explicit_proof:
                # Format: proof.\n<tactics>\nqed.
                proof_body = proof_content_raw[len('proof.'): -len('qed.')].strip()
            else:
                # Format: <tactics>\nqed. (implicit proof, no 'proof.' keyword)
                proof_body = proof_content_raw[:-len('qed.')].strip()
            
            # Normalize proof body so each tactic ends with '.' on its own line
            proof_body = normalize_proof_body(proof_body)

            # Count tactics: number of non-empty lines ending with '.'
            tactic_count = sum(
                1 for ln in proof_body.split("\n")
                if ln.strip() and ln.strip().endswith(".")
            )

            # Validate proof has content
            if tactic_count == 0:
                raise ValueError(
                    f"ERROR: Lemma '{item_name}' has empty proof body.\n"
                    f"Expected tactics between statement and qed."
                )
            
            # Sanity check: forbidden keywords in proof body
            FORBIDDEN_KEYWORDS = [
                'proof.', 'qed.', 'lemma ', 'local lemma', 'axiom ',
                'op ', 'type ', 'module ', 'theory ', 'section ',
                'end section', 'require ', 'clone '
            ]
            
            for line in proof_body.split('\n'):
                stripped = line.strip()
                for keyword in FORBIDDEN_KEYWORDS:
                    if stripped.startswith(keyword):
                        raise ValueError(
                            f"ERROR: Lemma '{item_name}' has forbidden keyword '{keyword}' in proof.\n"
                            f"This indicates nested proofs or parsing error.\n"
                            f"Line: {stripped[:100]}"
                        )
            
            # Rebuild canonical proof with explicit proof./qed.
            proof = f"proof.\n{proof_body}\nqed."

            result["content"].append({
                "type": "lemma",
                "name": item_name,
                "statement": statement,
                "proof": proof,
                "tactics": tactic_count,
            })
            pos = qed_pos
    
    # Compute total tactics for this file (sum over lemmas)
    total_tactics = sum(
        int(item.get("tactics", 0))
        for item in result["content"]
        if item.get("type") == "lemma"
    )
    result["tactics_total"] = total_tactics

    return result


def main():
    if len(sys.argv) != 3:
        print("Usage: python parse_easycrypt.py <input.ec> <output.json>")
        sys.exit(1)
    
    input_file = Path(sys.argv[1])
    output_file = Path(sys.argv[2])
    
    if not input_file.exists():
        print(f"Error: Input file '{input_file}' not found")
        sys.exit(1)
    
    if not input_file.suffix == '.ec':
        print(f"Warning: Input file '{input_file}' does not have .ec extension")
    
    print(f"Parsing {input_file}...")
    
    try:
        result = parse_easycrypt_file(input_file)
        
        # Count items
        lemma_count = sum(1 for item in result["content"] if item["type"] == "lemma")
        axiom_count = sum(1 for item in result["content"] if item["type"] == "axiom")
        tactics_total = result.get("tactics_total", 0)
        print(f"Found {lemma_count} lemmas, {axiom_count} axioms, {tactics_total} tactics")
        
        # Write JSON output
        with open(output_file, 'w') as f:
            json.dump(result, f, indent=2)
        
        print(f"Output written to {output_file}")
        
    except Exception as e:
        print(f"Error: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()
