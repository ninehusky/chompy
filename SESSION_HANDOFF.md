# Session handoff — FMCAD-2026 artifact prep (state as of 2026-05-07, REVISED)

> Resuming Claude Code on a different machine? Read this top-to-bottom, then
> begin from the **Next steps** section.

## Where we are (REVISED 2026-05-07 noon)

The `fmcad-2026` branch is at commit `f6790c7` ("Revert 'Revert
check_wraps_cleanly...'"). i.e. `check_wraps_cleanly` is BACK IN — the
validator is enabled. Branch tip is the post-revert-of-revert state.

**Verified earlier at the validator-OFF state** (commit `c6c3795`, no longer
HEAD): rebuilding from that state and running `--llm-usage baseline`
produced a `full_baseline.txt` with MD5
`1f9e7cb2fc80a5fff43b13688cbccb36` — byte-identical to all five cited 5/3
baselines. So we KNOW the 5/3 binary functionally matches HEAD-without-validator
on the deterministic baseline path. We've used that to confirm
`check_wraps_cleanly` was the only data-affecting drift.

## What we decided (REVISED)

**Keep the validator on. Do a full 5×7 rerun with the validator-on binary.**
The cited 5/3 + 5/5 data will be archived (not deleted — used as provenance)
and replaced with the new sweep's output. All 35 cells will then come from
ONE coherent binary state (today's HEAD = `f6790c7`, with `check_wraps_cleanly`
on).

This means paper Tables will report SLIGHTLY DIFFERENT numbers than the
original 5/3 sweep had:

- `baseline` row goes from 1579 rules to 1581 rules (verified earlier today;
  derivability claims, `forwards.can` against Halide and Caviar, do NOT change)
- LLM-using rows will produce new rule counts within natural LLM variance
  (probably small shifts from cited means)

The benefit: the artifact ships a single binary that PROVABLY produces the
shipped rulesets. No "different rows from different binaries" caveat needed
in ARTIFACT.md.

## Why we kept the validator (vs continuing with the revert)

- The validator is a real defensive fix for malformed LLM emissions
  (multi-`if` rules) that would panic `chop_assumption` later. Future work
  benefits from it.
- The 0.13% baseline rule-count shift is harmless (derivability identical).
- Reviewers re-running synthesis with the artifact's Docker image get exactly
  the data we ship.
- Empirically, the validator + existing `Assumption::new(...).unwrap()` call
  sites coexist fine: the 5/3 sweeps that included the validator (per
  user recollection) completed without panics. LLM-derived strings flow
  through `Rule::from_string` (`src/enumo/rule.rs:59`) which uses proper
  `Result` handling, not unwrap.

## Cross-row mode → paper-row mapping (for reference)

| Paper row | CLI `--llm-usage` | Code path (one-liner) |
|---|---|---|
| `baseline` | `baseline` | `og_recipe`, no LLM |
| `llm_terms_only` | `enum_only` | LLM provides 40 terms + 40 conditions, replaces workload |
| `with_enum` | `baseline_and_enum` | LLM appends 40 terms; conditions still from chompy |
| `filter_1` | `baseline_and_filter_1` | LLM clusters chompy candidates, top-1 per cluster |
| `filter_5` | `baseline_and_filter_5` | LLM clusters chompy candidates, top-5 per cluster |
| `enum + filter` | `baseline_with_filter_5_and_enum` | `with_enum` + filter top-5 |
| `llm-only` | `llm_only` | Single LLM prompt, z3-validated, no chompy |

LLM enumeration is hard-capped at 40 terms / 40 conditions per call site
(see `src/main.rs:58-63`). Filter `on_threshold = 10` (filter only fires if
`chosen_cond.len() > 10`); `top_k = {1, 5}` per the row name.

### What each row means (paper-style description)

This is the canonical row spec — what reviewers will see in the paper text
and what the code MUST faithfully implement. If at any point you're unsure
whether the code is doing the right thing for a row, this is the source of
truth.

- **baseline**: no LLM at all, whatsoever.
- **llm-only**: GPT prompted directly for whole rules; chompy bypassed; rules
  kept iff syntactically and semantically (z3) valid.
- **with_enum** (CLI: `baseline_and_enum`): terms come from chompy ∪ LLM
  (40 LLM terms appended per call site, capped); conditions still from chompy
  only. No other LLM use than this.
- **filter_1** (CLI: `baseline_and_filter_1`): enumeration like baseline; if
  a minimized candidate set exceeds 10 rules, LLM clusters them and the top 1
  per cluster is kept.
- **filter_5** (CLI: `baseline_and_filter_5`): enumeration like baseline; if
  a minimized candidate set exceeds 10 rules, LLM clusters them and the top 5
  per cluster is kept.
- **llm_terms_only** (CLI: `enum_only`): terms AND conditions both come
  exclusively from the LLM, chompy's enumerator is disabled.
- **enum + filter** (CLI: `baseline_with_filter_5_and_enum`): with_enum +
  filter_5-style filtering.

## Next steps (execute in order on the new machine)

### 1. Pull and verify

```bash
git fetch
git checkout fmcad-2026
git pull
git rev-parse --short HEAD   # should be f6790c7 or newer descendant
grep -c check_wraps_cleanly src/conditions/assumption.rs   # should print 3 (validator IS in the code)
```

Check that `Dockerfile` and `Dockerfile.update` are present, and that
`docker images chompy` exists or can be rebuilt.

### 2. Archive the existing 5/3 + 5/5 data

These are about to be superseded by the new sweep. Move (don't delete) them
so they remain available as provenance.

```bash
mkdir -p eval-archive/superseded_pre_revert_2026_05_07
mv eval-docker/2026_05_03_* eval-archive/superseded_pre_revert_2026_05_07/
mv eval-docker/2026_05_05_* eval-archive/superseded_pre_revert_2026_05_07/
```

Add a short README to `eval-archive/superseded_pre_revert_2026_05_07/`
explaining: these are the pre-revert sweep results; the cited 5/3 baseline
reproduces byte-identical from `c6c3795`'s binary, so they're preserved here
for provenance only and the FMCAD-2026 artifact uses the post-revert sweep.

Commit + push.

### 2.5. Pre-sweep code audit — verify rows match paper spec BEFORE 20+ hours of compute

This is read-only file inspection. No compute. Goal: catch any code-vs-paper
mismatch before kicking off the sweep, so we don't waste 20+ hours producing
data that doesn't match the spec.

#### 2.5a. Verify the CLI → `LLMUsage` mapping in `src/main.rs`

`src/main.rs:65-77` should map each CLI flag to the expected variant:

| Paper row | CLI flag | Expected `LLMUsage` variant |
|---|---|---|
| baseline | `baseline` | `LLMUsage::None` |
| enum_only | `enum_only` | `LLMUsage::EnumerationOnly(default_enum_cfg.clone())` |
| with_enum | `baseline_and_enum` | `LLMUsage::Enumeration(default_enum_cfg.clone())` |
| filter_1 | `baseline_and_filter_1` | `LLMUsage::Filter(default_filter_cfg.clone().with_top_k(1))` |
| filter_5 | `baseline_and_filter_5` | `LLMUsage::Filter(default_filter_cfg.clone().with_top_k(5))` |
| enum + filter | `baseline_with_filter_5_and_enum` | `LLMUsage::Combined([Filter(default_filter_cfg.clone()), Enumeration(default_enum_cfg.clone())])` |
| llm-only | `llm_only` | `LLMUsage::LLMOnly` |

```bash
sed -n '65,77p' src/main.rs   # eyeball the mapping
```

#### 2.5b. Verify the LLM caps and filter threshold in `src/main.rs`

```bash
grep -nE "with_on_threshold|with_num_conditions|with_num_terms" src/main.rs
```

Expected:
- `default_filter_cfg = LLMFilterConfig::default().with_on_threshold(10)` — filter only fires when the minimized candidate set exceeds 10 rules.
- `default_enum_cfg = LLMEnumerationConfig::default().with_num_conditions(40).with_num_terms(40)` — LLM emissions hard-capped at 40 terms / 40 conditions per call site.

#### 2.5c. Verify LLMOnly short-circuit at `src/main.rs:85-86`

`llm_only` mode must bypass the recipe machinery. Check:

```bash
sed -n '83,93p' src/main.rs
```

Expected: an `if matches!(llm_usage, LLMUsage::LLMOnly) { run_llm_only_recipe::<Pred>().await }` branch BEFORE the `match args.recipe { ... }` arm. If the conditional is missing, llm-only would fall into `og_recipe(LLMOnly).await` and the `assert!` in `run_workload` would panic immediately.

#### 2.5d. Verify the LLMOnly assertion in `src/recipe_utils.rs`

The recipe machinery must defensively reject LLMOnly:

```bash
grep -nA2 "LLMOnly must be handled at the top level" src/recipe_utils.rs
```

Expected: `assert!(!matches!(llm_usage, LLMUsage::LLMOnly), ...)` near `run_workload`.

#### 2.5e. Verify the conditions-from-LLM gate in `src/recipe_utils.rs`

Only `EnumerationOnly` should fetch LLM conditions. Other LLM-using modes
(Enumeration, Combined-with-Enumeration) must use chompy-only conditions.

```bash
grep -nA1 "matches!(cfg.clone(), LLMUsage::EnumerationOnly" src/recipe_utils.rs
```

Expected: `let conditions = if matches!(cfg.clone(), LLMUsage::EnumerationOnly(_)) {` — this gate is what enforces "with_enum and enum+filter use chompy-only conditions" per the paper. If the gate is missing or expanded, with_enum and enum+filter would also fetch LLM conditions, contradicting the paper.

#### 2.5f. Verify the validator (`check_wraps_cleanly`) is ON

```bash
grep -c check_wraps_cleanly src/conditions/assumption.rs   # MUST print 3
```

3 hits = function definition + 2 call sites in `Assumption::new` and `Assumption::new_unsafe`. If the count is 0, the validator is reverted; STOP and verify branch state.

#### 2.5g. Verify the LLM model is gpt-5.4 (intentional bump)

```bash
grep -c '"gpt-5.4"' src/llm.rs   # should print 8
```

`gpt-5.4` is the intended model for this artifact. If it's `gpt-4o`, paper text is referencing the older model and code drifted; reconcile before sweep.

#### 2.5h. Verify Z3 4.12.1 pin in Dockerfile

```bash
grep -nE "Z3_VERSION|z3-4\." Dockerfile Dockerfile.update
```

Expected: 4.12.1 referenced in both files. This is the Z3 version that empirically reproduced the original eval.

#### 2.5i. Verify `Cargo.lock` exists and isn't drifted

```bash
ls -la Cargo.lock           # must exist; mtime should be ≥ 2026-04-17
git ls-files Cargo.lock     # may print empty (still gitignored) — fine
```

Cargo.lock is gitignored. If it's missing on a fresh clone, `cargo build` will resolve fresh — could pick up a different egg or z3-sys patch version. If you don't see Cargo.lock locally, STOP and copy from the laptop's repo (or `git add -f` it before the sweep starts).

#### 2.5j. Verify `.gitignore` exception placement

```bash
tail -10 .gitignore
```

Expected: the `!eval-docker/**/*.txt` and `!eval-docker/**/*.log` exceptions appear AFTER the broad `*.txt` and `*.log` rules. If they're reordered above, the sweep's rulesets and logs won't be tracked, defeating the artifact.

#### Stop signals from this audit

If any of these fail before kicking off:

- `LLMUsage` mapping doesn't match the table in 2.5a → code drift; STOP.
- `check_wraps_cleanly` count ≠ 3 → unintended revert state; STOP.
- LLMOnly short-circuit missing in main.rs → would panic on llm-only; STOP.
- `EnumerationOnly` conditions-gate is broadened → would fetch conditions for with_enum / enum+filter, contradicting paper; STOP.
- Model name is not `gpt-5.4` → paper-vs-code mismatch; reconcile before sweep.
- Z3 not pinned to 4.12.1 → derivability could drift; STOP.

Only after **all 2.5a-2.5j checks pass** do you proceed to step 3 (edit
`run_the_eval.py`) and step 5 (kick off the sweep).

### 3. Edit `python/run_the_eval.py` for the full sweep

Change `usages` to all 7 modes:

```python
usages = [
    "baseline",
    "enum_only",
    "baseline_and_enum",
    "baseline_and_filter_1",
    "baseline_and_filter_5",
    "baseline_with_filter_5_and_enum",
    "llm_only",
]
```

Don't commit this (it's the eval driver, not the artifact contract).

### 4. Verify untracked smoke-test dirs are cleaned

Delete or leave the leftover `eval-docker/2026_05_07_*` dirs. They're untracked
test outputs from this session. They won't affect the sweep.

### 5. Kick off the full 5x7 sweep under caffeinate

The `python/run_overnight.sh` script handles 5 sweeps + OOM recovery
automatically. Pass MODES to override its default and TARGET_RUNS to 5:

```bash
export OPENAI_API_KEY=sk-...   # required
export TARGET_RUNS=5
export MODES="baseline llm_only enum_only baseline_and_enum baseline_and_filter_1 baseline_and_filter_5 baseline_with_filter_5_and_enum"
caffeinate -dis nohup bash python/run_overnight.sh > /tmp/chompy_overnight.log 2>&1 &
disown
```

Output lands in `eval-docker/<timestamp>/full/<mode>/`. Check progress with
`tail -F /tmp/chompy_overnight.log`.

### 6. Post-sweep audit (REQUIRED before declaring artifact ready)

After the 5×7 sweep completes (~20-25 hours), run this audit. It verifies
that the data on disk actually matches the paper specification. If any
check trips a STOP signal, archive the partial sweep and ping the user
before remediation.

#### 6a. Completeness — all 35 cells have ruleset + 2 derivability JSONs

```bash
for d in eval-docker/2026_05_07_*/full/*/; do
  m=$(basename "$d")
  txt="$d/full_${m}.txt"
  hal="$d/full_${m}_against_halide.json"
  cav="$d/full_${m}_against_caviar.json"
  [ -s "$txt" ] && [ -f "$hal" ] && [ -f "$cav" ] && echo "OK  $d" || echo "MISS $d"
done
```

Should print `OK` for all 35 (5 runs × 7 modes). Any `MISS` → recovery via
`run_overnight.sh recover_mode` or manual standalone re-run.

#### 6b. Within-row binary consistency — same llm_usage Debug print

Every mode's 5 runs should have a byte-identical `llm_usage:` Debug print.
If they differ, some run was from a different binary state — STOP.

```bash
for mode in baseline llm_only enum_only baseline_and_enum \
            baseline_and_filter_1 baseline_and_filter_5 \
            baseline_with_filter_5_and_enum; do
  echo "=== $mode ==="
  for log in eval-docker/2026_05_07_*/full/$mode/full_$mode.log; do
    grep -m1 "^llm_usage:" "$log" 2>/dev/null
  done | sort -u | wc -l   # MUST be 1 (or 0 for baseline which prints differently)
done
```

For baseline, the equivalent check is byte-identity:
```bash
md5 eval-docker/2026_05_07_*/full/baseline/full_baseline.txt
# All 5 should print the same hash. Expected: 1581-rule ruleset, deterministic
# (specific MD5 will differ from the 5/3 cited 1f9e7cb2... because the validator
# is now on; what matters is that all 5 today match each other).
```

#### 6c. Per-row sanity check — rule counts and LLM call counts

Each row's 5 runs should land within the expected ranges below. Runs
outside these ranges aren't necessarily wrong (LLM variance), but very
large deviations suggest something drifted.

| Paper row | CLI mode | Expected rule count range | Term LLM calls per run | Cond LLM calls per run |
|---|---|---|---|---|
| baseline | `baseline` | exactly **1581** (deterministic, validator-on) | 0 | 0 |
| llm-only | `llm_only` | ~100-150 | N/A | N/A — single GENERATE_RULES_PROMPT call |
| with_enum | `baseline_and_enum` | ~1450-1600 | ~13 | **0** (chompy-only conditions) |
| filter_1 | `baseline_and_filter_1` | ~830-900 | 0 | 0 — but ~50-65 filter batch calls |
| filter_5 | `baseline_and_filter_5` | ~1380-1480 | 0 | 0 — but ~50-65 filter batch calls |
| enum_only | `enum_only` | ~150-250 | ~13 | ~13 |
| enum + filter | `baseline_with_filter_5_and_enum` | ~1300-1500 | ~13 | **0** + ~50-65 filter batch calls |

**Critical**: only `enum_only` should have `[get_llm_conditions] kept N/40`
log lines. If any other LLM-using mode has them, the `EnumerationOnly`-only
conditions gate in `get_llm_ammo` (`src/recipe_utils.rs:421`) has been
broadened — that contradicts the paper spec for `with_enum` and `enum + filter`
which both say "conditions still from chompy only." STOP and reconcile.

```bash
echo "=== modes that fetched LLM conditions (should be enum_only ONLY) ==="
for d in eval-docker/2026_05_07_*/full/*/; do
  m=$(basename "$d")
  log="$d/full_${m}.log"
  if grep -q "\[get_llm_conditions\] kept" "$log" 2>/dev/null; then
    echo "  $d"
  fi
done | sort -u
```

#### 6d. Headline derivability matches paper claims

The cited 5/3 sweep had `forwards.can` against Halide of 48 for `baseline`
and 32 for the Caviar baseline. These should be unchanged by the validator
(verified earlier today on a single run). Other rows' `forwards.can` may
shift slightly due to LLM variance.

```bash
python3 - <<'PY'
import json, glob, os
from collections import defaultdict
totals = defaultdict(lambda: defaultdict(list))
for h in glob.glob('eval-docker/2026_05_07_*/full/*/full_*_against_*.json'):
    parts = h.split('/')
    mode = parts[-2]
    target = 'halide' if 'halide' in h else 'caviar'
    j = json.load(open(h))
    totals[mode][target].append(len(j.get('forwards',{}).get('can',[])))
for mode in sorted(totals):
    h = totals[mode]['halide']; c = totals[mode]['caviar']
    print(f"  {mode:35s}  halide forwards.can mean={sum(h)/len(h):.1f} runs={h}")
    print(f"  {' '*35}  caviar forwards.can mean={sum(c)/len(c):.1f} runs={c}")
PY
```

Expected anchors (within ±2 due to natural variance for LLM rows):
- `baseline` Halide: 48 (exact), Caviar: 32 (exact)
- LLM-using rows: should be in the same ballpark as the cited means
  (you can compare against `eval-archive/superseded_pre_revert_2026_05_07/`'s
  derivability JSONs for reference)

#### 6e. Stop signals — do NOT declare artifact ready if any of these fire

1. Any baseline run produces ≠ 1581 rules.
2. The 5 baselines aren't byte-identical to each other.
3. `enum_only` doesn't produce both term AND condition prompts (~13 each).
4. Any LLM-using mode other than `enum_only` produces `get_llm_conditions` log lines.
5. Any row's `llm_usage:` Debug print differs across its 5 runs.
6. `baseline` Halide `forwards.can` ≠ 48 or Caviar ≠ 32.
7. Any row's `forwards.can` mean shifts by ≥ 5 from the cited 5/3 mean
   (suggests something other than LLM variance is at play).

If a stop signal fires, archive the affected runs to
`eval-archive/aborted_<reason>_<date>/` and ping the user with the specific
signal that fired before doing anything else.

#### 6f. Update paper numbers

If the audit passes, regenerate Tables 1/2 from the new data:

```bash
python3 python/summarize_runs.py eval-docker out.csv
```

Compare against the 5/3 cited numbers (preserved at
`eval-archive/superseded_pre_revert_2026_05_07/`). Note any numerical
shifts in the paper text. Most should be small (within ±5% on rule counts;
derivability `forwards.can` values should be within ±2).

## Critical context (worth re-reading)

### Why `check_wraps_cleanly` is KEPT (revised plan)

The validator (added in commit `a4db5de`) is data-affecting: HEAD-with-validator
produces 1581 baseline rules; HEAD-without-validator produces 1579 (matches
cited 5/3 baseline byte-identical). The 5/3 binary empirically did not have
this validator on for the baseline run.

We considered shipping HEAD-without-validator to match cited data, but
chose to keep the validator on because:

1. It's a defensive fix for malformed LLM emissions; useful going forward.
2. The full 5×7 rerun under one binary state is methodologically cleaner
   than retroactively reconstructing the original binary.
3. Derivability claims (`forwards.can` against Halide and Caviar) don't shift
   between validator-on and validator-off baseline runs (verified: 48 / 32
   in both).

### Artifact contract

- Ship the 35 NEW rulesets from this rerun (`.txt`) + derivability JSONs +
  logs + Dockerfile pinned to Z3 4.12.1.
- Reviewers reproduce Table 1 by running derivability against shipped
  rulesets. Bit-identical resynthesis is not promised for LLM-using rows
  (LLM is non-deterministic by design).
- For deterministic `baseline`, today's HEAD (`f6790c7`) reproduces 1581 rules
  byte-identical on every run.

Earlier artifact (replay-with-cache) was rejected for fragility under prompt
drift; this contract sidesteps that by not putting the LLM in the eval loop.

### Key gotchas

- `Cargo.lock` is gitignored (line 17 of `.gitignore`). Local mtime is
  April 17. If a reviewer clones fresh and `Cargo.lock` resolves differently,
  derivability could shift. Consider `git add -f Cargo.lock` before final
  artifact submission.
- `caffeinate` only blocks sleep; it does NOT prevent CPU throttling under
  Apple Silicon's low-battery mode. Keep on AC.
- `*.txt` and `*.log` are gitignored globally; `.gitignore` has explicit
  exceptions at the bottom (`!eval-docker/**/*.{txt,log}` etc.) for the
  artifact data. Don't reorder them or `*.log` will eat them again.

### Within-row consistency (verified for the 5/3 sweep)

All 5 runs of each row had byte-identical `llm_usage:` Debug-print and
identical `kept N/40` denominators. After the new sweep, re-verify with the
audit pattern from this conversation (find ... -path '*/full/<mode>/*.log',
extract `llm_usage:` line, confirm all 5 match).
