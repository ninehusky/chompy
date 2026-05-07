# Superseded pre-revert sweep results

These directories contain the 5/3 and 5/5 sweep runs produced before the
`check_wraps_cleanly` revert.

## Why archived

The FMCAD-2026 artifact uses a single post-revert sweep for coherence: all 35
runs (5 reps × 7 modes) come from one known binary state. These results are
preserved here for provenance only.

## What "pre-revert" means

Commit `a4db5de` introduced a `check_wraps_cleanly` validator that turned out
to be data-affecting in baseline mode: with the validator, the binary produces
1581 baseline rules; without it, 1579 (matching the cited 5/3 data
byte-identical). The revert is in commit `c6c3795`. The post-revert binary is
what the FMCAD-2026 artifact ships.

## Byte-identity verification

The cited 5/3 baseline (`full_baseline.txt`, MD5 `1f9e7cb2fc80a5fff43b13688cbccb36`)
reproduces byte-identical from the post-revert binary at `c6c3795`. This was
verified before starting the fresh sweep.

## Contents

- `2026_05_03_*/` — five runs from 2026-05-03 (baseline, filter, some LLM modes)
- `2026_05_05_*/` — five runs from 2026-05-05 (llm_only single-prompt path)

The llm_only runs in `2026_05_03_*/` used an earlier hybrid code path and were
already separately archived to `eval-archive/llm_only_pre_single_prompt_2026_05_04/`
before these directories were moved here.
