# Session handoff — FMCAD-2026 artifact prep (state as of 2026-05-07)

> Resuming Claude Code on a different machine? Read this top-to-bottom, then
> begin from the **Next steps** section.

## Where we are

The `fmcad-2026` branch is at commit `c6c3795` ("Revert check_wraps_cleanly to
restore byte-reproducibility of cited 5/3 baseline"). The repo is clean except
for some untracked `eval-docker/2026_05_07_*` directories from
investigation/test runs that can be deleted.

**Verified at this state**: rebuilding `chompy:latest` from `c6c3795` and
running `--llm-usage baseline` produces a `full_baseline.txt` whose MD5 is
`1f9e7cb2fc80a5fff43b13688cbccb36` — byte-identical to all five cited 5/3
baselines. Halide and Caviar derivability JSONs are also byte-identical.

## What we decided

**Re-run the full 5×7 sweep** with the current binary (post-revert) to produce
a coherent dataset where every cited number comes from one consistent build.
This eliminates the "different rows produced from different binaries" worry
that the 5/3+5/5 split has.

The existing 5/3 + 5/5 data should be archived (NOT deleted — used as
provenance) and replaced with the new sweep's output.

## Why we decided that

- The 5/3 binary's exact code state isn't fully reconstructable (uncommitted
  source at the time, ambiguous commit messages). We can verify byte-identity
  with the deterministic `baseline` row (and we have), but for LLM-using rows
  we can't verify the historical binary state.
- Running all 7 rows × 5 from one known binary makes the artifact contract
  airtight: "build this Docker image, run the pipeline, you get rulesets in
  the variance range we cite."
- Time budget allows: ~20-25 hours wallclock, deadline is Monday EOD, ~60+
  hours of slack from this commit.

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
git rev-parse --short HEAD   # should match c6c3795 or newer revert-preserving commit
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

### Why `check_wraps_cleanly` is reverted

The validator (added in commit `a4db5de`) was data-affecting in baseline mode:
HEAD-with-validator produces 1581 baseline rules; HEAD-without-validator
produces 1579 (matches cited 5/3 data byte-identical). The 5/3 binary
empirically did not have this validator. To make today's binary match the
cited data, the revert is mandatory.

The validator's intended purpose (rejecting malformed LLM-emitted assumption
patterns earlier in the pipeline) is real but should be re-introduced AFTER
the FMCAD submission, on a follow-up branch.

### Artifact contract (Option B from discussion)

- Ship the 35 rulesets (`.txt`) + derivability JSONs + logs + Dockerfile
  pinned to Z3 4.12.1.
- Reviewers reproduce Table 1 by running derivability against shipped
  rulesets. We do NOT promise bit-identical resynthesis from re-runs.
- Deterministic rows (`baseline`) reproduce byte-identical from the frozen
  pipeline. LLM-using rows reproduce within natural LLM variance.

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
