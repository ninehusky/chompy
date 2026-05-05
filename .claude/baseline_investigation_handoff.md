# Baseline mismatch investigation — handoff

## Context
User (Andrew) asked me to figure out why the `baseline` `--llm-usage` run no longer matches `original-eval/`. The README says baseline is the "ground truth" that should reproduce across machines. It currently does not.

User left for dinner mid-investigation. They restarted Claude Code with `claude remote-control` so phone push notifications work. **Text them via `PushNotification` only when there's a real finding or a blocker — not for routine progress.**

## What's already established

### Baseline-run rule counts
| Run | Rules |
|---|---|
| `original-eval/run_one/full/baseline/full_baseline.txt` | 1579 |
| `original-eval/run_two/.../full_baseline.txt` | 1579 |
| `original-eval/run_three/.../full_baseline.txt` | 1579 |
| `eval/2026_04_28_18_34/full/baseline/full_baseline.txt` (most recent) | **1577** |
| `eval/2026_04_27_12_57/full/baseline/full_baseline.txt` | 1564 |
| `eval/2026_04_27_12_51/...` | 0 (failed run) |

The 3 original-eval baselines are **byte-identical** when sorted (`diff` returns empty between any pair). So baseline really is meant to be deterministic.

### How much actually differs in the latest run
Comparing `original-eval/run_one/full/baseline/full_baseline.txt` against `eval/2026_04_28_18_34/full/baseline/full_baseline.txt`, sorted:

- 1328 rules match exactly between original and current
- 500 lines differ in the diff (~250 rules in each direction)
- Many diffs look like **canonicalization variants of equivalent rules** — same LHS/RHS pair but with rearranged max/min args (`(max ?a ?b)` vs `(max ?b ?a)`) or different but seemingly equivalent conditions (`(!= ?b 0)` vs `(<= 0 ?a)`)
- But not all — some rules appear/disappear entirely

### Derivability — this is the bigger concern
From `python3 python/summarize.py eval/2026_04_28_18_34 /tmp/cur.csv`:

```
run_type,num_rules,caviar_derivability,halide_derivability,runtime_seconds
baseline,1577,58.3,52.2,1956.0
```

vs the original (from README):
```
baseline,1579.0,71.1,57.1,1549.3
```

That's a **~13pp drop in caviar derivability and ~5pp in halide derivability**. The number of rules barely moved (1577 vs 1579), so the rules in the current run really are *weaker*, not just renamed/reordered. Something semantic changed.

## Local uncommitted modifications (likely culprits)

```
M python/run_the_eval.py       |   1 +
M src/conditions/assumption.rs |  27 ++-
M src/llm.rs                   | 407 ++++++++++++++++++++++++++++---------------
M src/main.rs                  |   1 +
M src/recipe_utils.rs          |  49 ++++++
```

- `src/llm.rs` shouldn't matter for baseline (`--llm-usage baseline` → `LLMUsage::None` → skips the LLM code paths in `recipe_utils::run_workload`).
- `src/recipe_utils.rs` (+49 lines) is the most suspicious — it's where `run_workload`/`run_workload_internal` live, which baseline does execute. **Read the diff (`git diff HEAD -- src/recipe_utils.rs`) and look for changes to behavior that affect rule selection / minimization.**
- `src/conditions/assumption.rs` (27 lines changed) could affect conditional rules, which baseline does produce (most of the differing rules in the diff are conditional).
- The diffs are saved to `/tmp/recipe_utils_diff.txt`, `/tmp/assumption_diff.txt`, `/tmp/main_diff.txt` (74/66/12 lines respectively) for quick reference, but they may not survive a tmp cleanup — re-derive from git if needed.

## Suggested next steps

1. **Read the actual local diffs** (not the current file state):
   - `git diff HEAD -- src/recipe_utils.rs`
   - `git diff HEAD -- src/conditions/assumption.rs`
   - `git diff HEAD -- src/main.rs`
   Look for behavior changes that touch rule synthesis / minimization / conditional-rule handling. Don't get distracted by `src/llm.rs` — baseline doesn't exercise it.

2. **Confirm the modifications are the cause** by stashing them and running a fresh baseline from a clean tree:
   - `git stash`
   - `cargo run --release --bin ruler -- --recipe full --llm-usage baseline --output-path /tmp/clean_baseline.txt` (~25-30 min on this machine; baseline does NOT need OPENAI_API_KEY)
   - Diff `/tmp/clean_baseline.txt` against `original-eval/run_one/full/baseline/full_baseline.txt`
   - If clean tree matches original → modifications are the cause. If clean tree also diverges → it's a build-env issue (z3, egg, deps).
   - **Restore with `git stash pop`** when done.

3. **If modifications are confirmed cause**: bisect the diff — revert pieces of `recipe_utils.rs` / `assumption.rs` to find the specific change that breaks baseline.

4. **If clean tree also diverges**: look at git log for `Cargo.lock`, `rust-toolchain`, and any deps. The most recent commit `b0058ec` ("Fix z3-sys build on macOS with AppleClang 21 / CMake 4.x") is suspicious — z3 version changes can affect rule-validity checking and therefore which candidates survive minimization. Check if original-eval was generated before that fix.

5. **Text Andrew via `PushNotification`** when you reach a diagnosis ("modifications X cause baseline divergence" / "clean tree also diverges, suspect z3" / etc.).

## Memory context already loaded
- `~/.claude/projects/-Users-andrew-research-chompy/memory/MEMORY.md` — index
- `feedback_eval_llm_cache.md` — eval runs use real LLM (cache is the artifact); doesn't apply to baseline
- `project_z3_build_fix.md` — relevant if you suspect z3 env issues

## Tasks already created (in current session, won't survive restart)
1. Diff recent baseline vs original-eval baseline (in_progress)
2. Inspect local src/ modifications that affect baseline (pending)
3. Trace baseline code path (pending)
4. Diagnose and report root cause (pending)

Recreate as TaskCreate items in the new session if useful.
