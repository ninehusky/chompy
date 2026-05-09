# Archived `llm_only` results — pre single-prompt fix

These five `llm_only` directories were produced on 2026-05-03 with a hybrid
implementation that does **not** match the row's intended semantics. They are
preserved here for reference only and should not be cited as `llm_only` numbers.

## Why these are wrong

`--llm-usage llm_only` was meant to be: a single LLM prompt
(`GENERATE_RULES_PROMPT` in `src/llm.rs`), parsed, kept iff syntactically and
semantically (z3) valid — no chompy enumeration, no minimization, no recipe.

What actually happened in `og_recipe` under `llm_only`:

- Each `run_workload(...)` call short-circuited to `run_llm_only_workload`,
  issuing its own `GENERATE_RULES_PROMPT` call. So instead of one LLM call,
  the recipe issued ~5 (one per `run_workload` site).
- Each `recursive_rules_cond(...)` call did **not** special-case `LLMOnly` —
  it ran plain baseline chompy on the language grammar, with no LLM input at
  all. About 7 of the ~12 inference units in `og_recipe` fell into this path.

So each archived row is `LLM(run_workload sites) ∪ baseline(recursive_rules_cond sites)`
with the LLM portion split across ~5 independent prompts. Neither "pure LLM"
nor "single prompt".

## Source commit

The hybrid behavior lived in:
- `src/recipe_utils.rs::run_workload` (the LLMOnly short-circuit at the top)
- `src/recipe_utils.rs::recursive_rules_cond_internal` (no LLMOnly arm in the
  workload/conditions match — fell through to the baseline `_` arm)

See `git log -- src/recipe_utils.rs src/main.rs` around 2026-05-04 for the fix.
