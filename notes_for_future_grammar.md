# Notes for Future Grammar / Debug Sessions

## 1. Pipeline Entry Points

### Grammar normalization & reachability
- Command: `python3 out/inspect_raw_grammar.py`
- Reads `out/grammar_raw.json`
- Seeds live in `inspect_raw_grammar.py` (search for `seed_heads =`). Add new heads when structural keywords are missing.
- Expression heads come from `find_structure_heads`. Adjust the `patterns` / `extra` lists to change what collapses to `EXPR`.
- Synthetic helpers (aliases, list recursions, `Line` start symbol, etc.) are implemented near `alias_productions`, `inject_list_recursions`, and `add_line_start`.

### Tests / tokenizer
- Command: `python3 tests/test_grammar_examples.py`
- Consumes `out/grammar_reduced.json` and `out/grammar_reduced_expr.json`.
- `tokenize_line` owns EXPR collapsing controls (`EXPR_START_TOKENS`, `EXPR_END_TOKENS`, `FORBIDDEN_EXPR_START_TOKENS`, etc.).
- Script supports `--mode strict` (default) and `--mode cfg`. CFG mode disables the bespoke tokenizer so you can see the raw CFG acceptance (103/103 good lines pass; 6/23 bad lines slip through).
- `build_productions` + `EarleyParser` sit in the same file; if structure is missing, fix the generator rather than the parser.

## 2. Debug Workflow

### When a valid line fails
1. Run `python3 tests/test_grammar_examples.py` and note failing line numbers.
2. In a REPL, call `tokenize_line(...)` on that text to inspect the token stream.
3. If tokens look wrong, fix the tokenizer (usually EXPR start/end boundaries).
4. If tokens look right, run `EarleyParser.parse(tokens)` to locate the missing nonterminal; add it via aliases, seeds, or collapse rules as appropriate.
5. Regenerate (`python3 out/inspect_raw_grammar.py`) and rerun tests.

### When an invalid line passes
1. Tokenize and confirm whether the structural tokens are truly legal. If SSReflect-style constructs sneak in (e.g., `/=`), add guards to `FORBIDDEN_EXPR_START_TOKENS` or the HAVE check.
2. If the tokens are legitimate, prune the grammar by collapsing the offending heads (update `find_structure_heads`).
3. Regenerate + retest.

## 3. Regeneration Checklist
- After modifying `inspect_raw_grammar.py`:
  - `python3 out/inspect_raw_grammar.py`
  - `python3 tests/test_grammar_examples.py`
  - Verify stats (`good.ec`: 73/73 historic baseline, now 103/103; `bad.ec`: 0/23).
  - Spot-check tricky lines via the helper snippets.

## 4. Tokenizer Gotchas
- Literal vs pattern priority: handled in `build_token_specs` using an `is_literal` flag so keywords don’t eat identifiers.
- Expressions stay opaque: tokenizer just finds EXPR spans; nesting tracked via `expr_depth`.
- Special cases:
  - `HAVE` must be followed by intro patterns or a colon; bare `have :=` is rejected.
  - Restricted contexts (`CALL`, `APPLY`) disallow `RAW_FALLBACK` (blocks `/=` shorthands).
  - `EXPR_START_TOKENS` includes structural keywords (`BYEQUIV`, `BYPHOARE`, `MOVE`, etc.) so the remainder collapses cleanly.

## 5. Structural Coverage Reminders
- Seeds already cover tactic/proof heads, statements, commands, and helpers. Add new EasyCrypt keywords to `seed_heads`.
- Collapsed expression heads include `im_stmt*`, `inline*`, rewrite options, etc. If a non-structural symbol leaks into `grammar_reduced_expr.json`, consider adding it to the collapse list.
- Synthetic rules currently injected:
  - `Line ::= tactic DOT | tactics_or_prf DOT | stmt DOT | stmt | QED DOT`
  - `tactic_core_r` synthetic variants: `RND`, `SIM`, `MOVE EXPR`, `RND EXPR`
  - `subtactics -> subtactic SEMICOLON subtactics` recursion for tactic chains
- Tokenizer additions since the last run:
  - `EXPR_START_TOKENS` now includes `APPLY`, `EXACT`, `WHILE`, `ASYNC`
  - Restricted contexts: `{CALL, APPLY}`; seeing a lone `/` inside them raises immediately
  - `APPLY` followed by `WITH` is rejected outright
  - Once `expr_mode` activates due to a non-structural token, it stays active for the rest of that opaque span (`swap 3 3.`, `while (...) (...)`, etc.)

### Closing the CFG-only gap
- CFG-only mode still lets a few `bad.ec` lines parse. Two ways to seal it:
  1. **Keep the bespoke tokenizer** (strict mode) in front of the CFG decoder—the setup used by `tests/test_grammar_examples.py`.
  2. **Desugar `EXPR` inside the grammar** so the CFG sees the complete expression/form syntax. This adds thousands of productions and slows decoding, but it’s the only way to enforce those lexical constraints without a custom lexer.

---

Keep these touchpoints handy so future debugging sessions can resume quickly without re-deriving the entire state.

