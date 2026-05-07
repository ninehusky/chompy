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

| Paper row | CLI `--llm-usage` | Code path |
|---|---|---|
| `baseline` | `baseline` | `og_recipe`, no LLM |
| `enum_only` | `enum_only` | LLM provides 40 terms + 40 conditions, replaces workload |
| `with_enum` | `baseline_and_enum` | LLM appends 40 terms; conditions still from chompy |
| `filter_1` | `baseline_and_filter_1` | LLM clusters chompy candidates, top-1 per cluster |
| `filter_5` | `baseline_and_filter_5` | LLM clusters chompy candidates, top-5 per cluster |
| `enum + filter` | `baseline_with_filter_5_and_enum` | `with_enum` + filter top-5 |
| `llm-only` | `llm_only` | Single LLM prompt, z3-validated, no chompy |

LLM enumeration is hard-capped at 40 terms / 40 conditions per call site
(see `src/main.rs:58-63`). Filter `on_threshold = 10` (filter only fires if
`chosen_cond.len() > 10`); `top_k = {1, 5}` per the row name.

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

### 6. After the sweep completes (~20-25 hours)

Verify all 35 runs have non-empty `.txt` and both derivability JSONs:

```bash
for d in eval-docker/2026_05_07_*/full/*/; do
  m=$(basename "$d")
  txt="$d/full_${m}.txt"
  hal="$d/full_${m}_against_halide.json"
  cav="$d/full_${m}_against_caviar.json"
  [ -s "$txt" ] && [ -f "$hal" ] && [ -f "$cav" ] && echo "OK  $d" || echo "MISS $d"
done
```

Then update paper Tables 1/2 numbers from the new data using
`python/summarize_runs.py eval-docker out.csv`.

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
