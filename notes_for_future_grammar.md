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

### Literal EBNF export
- Command: `python3 out/emit_literal_grammar.py`
- Generates `out/grammar_reduced_expr_literals.ebnf`, where every token name has a real terminal rule so `transformers-cfg` can expand beyond EOS.
- Pulls literal/pattern data from `grammar_raw.json`; punctuation tokens are injected via overrides inside the script, and we inject `WS_OPT ::= (WS_CHAR)*` so arbitrary indentation matches without help from the Menhir lexer.
- `EXPR` now expands via `EXPR_CHAR ::= [^\r\n]` so the CFG no longer relies on an opaque dangling symbol.
- Tokens that still lack literal coverage fall back to placeholders `__token__`; rerun with `--strict` to make the script fail instead (useful once you start desugaring identifier/number classes properly).

### Literal CFG sanity test
- Command: `python3 tests/test_cfg_strings.py`
- Regenerates the grammar artifacts (including the literal EBNF) unless `--skip-refresh` is passed.
- Builds `transformers-cfg`'s `StringRecognizer` directly from `grammar_reduced_expr_literals.ebnf` and parses every line of `good.ec` / `bad.ec` without using our bespoke tokenizer.
- Mirrors the reporting style of `tests/test_grammar_examples.py`: good lines must all succeed; bad lines currently show which entries still sneak through when lexical policing is disabled (expected to fail until we desugar more structure).

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

## 6. Minimal Line Grammar Playbook

Use this when iterating on the deliberately tiny line-by-line CFG emitted by `out/emit_minimal_grammar.py`. The goal is to keep the number of productions comfortably below 100 while filtering out obviously invalid snippets such as SSReflect comment shorthands (`apply(*`, `have=>(/((*`, etc.).

### High-level goals
- Match each input line independently; no state should leak across newlines.
- Accept as many curated lines from `grammar_examples/good_simple.ec` as possible.
- Reject noisy constructs in `grammar_examples/bad.ec`, prioritizing SSReflect comment shorthands, unterminated parenthesis blobs, and `/=` sugar.
- Maintain readability inside `emit_minimal_grammar.py`; prefer tiny helpers or character-class tweaks over broad rewrites.

### Workflow for each tweak
1. **Edit the emitter** (`out/emit_minimal_grammar.py`) instead of touching the generated `.ebnf` file directly.
2. **Regenerate the artifact** with `python3 out/emit_minimal_grammar.py` so `out/minimal_easycrypt.ebnf` stays in sync.
3. **Run the smoke test**: `python3 tests/test_minimal_cfg.py`.
   - Default tolerances: at most 6 rejected good lines (`--max-good-fail`), at most 3 accepted bad lines (`--max-bad-pass`).
   - Current baseline (before expanding coverage) is `accepted=89 / rejected=21` for `good_simple.ec`; aim to reduce the rejection list when possible.
4. **Interactively probe edge cases** with `python3 tests/interactive_minimal_cfg.py`. Use `:batch` to feed text, `:reset` to start a new line, and `:reset hard` (or the new `--reset hard` CLI flag) to reload the emitter after editing it.
5. **Document tricky cases** by appending notes to this file so future iterations know why certain exclusions exist.

### When a new syntax fragment appears
1. Drop the exact line into `grammar_examples/good_simple.ec` (if it should pass) or `grammar_examples/bad.ec` (if it should fail).
2. Re-run `tests/test_minimal_cfg.py` to see whether the grammar already handles it.
3. If a valid line fails, expand the minimal grammar just enough to cover that structural pattern (e.g., allow `inline*` followed by whitespace, widen safe character classes, or add a single helper production).
4. If an invalid line passes, tighten the relevant tail production or separator so the specific nuisance stops matching (never rely on lookahead; everything is plain EBNF).
5. Keep an eye on production count—favor reusing existing nonterminals and character classes over minting brand new ones.

### Testing checklist before handing off
- `python3 out/emit_minimal_grammar.py`
- `python3 tests/test_minimal_cfg.py`
- Optional: `python3 tests/interactive_minimal_cfg.py --reset hard` to confirm the constraint rebuilds cleanly after your edits.

This section is the snapshot of “what we care about” for the minimalist CFG; update it anytime the goals, tolerances, or workflows change so future iterations have the right context without digging through chat logs.

#### IMPORTANT
You should only update the grammar (EBNF file and its emitter python), not the test files when trying to make more statements to pass or fail. The goal is to improve the standalong grammar.

You can always refer to grammar_raw.json to understand the precise syntax for a tactic.

