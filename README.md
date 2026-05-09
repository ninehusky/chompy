# Conditional Rewrite Rule Synthesis Using E-Graphs and LLMs (FMCAD 2026 artifact)

This is the artifact for our FMCAD 2026 paper *"Conditional Rewrite Rule
Synthesis Using E-Graphs and LLMs"*, which extends theory exploration to
support (1) conditional rule synthesis and (2) LLM-guided enumeration and
filtering.

The artifact targets the three FMCAD badges:

- **Available** — hosted on Zenodo, DOI `10.5281/zenodo.17173426`.
- **Functional** — every claim in the paper can be re-verified from this
  repository in a few minutes to a few hours, with steps ordered by trust
  (see *Reproducing Table 1* below).
- **Reusable** — Chompy can be extended to other domains via the
  `SynthLanguage` trait (see *Reusability* below).

## Overview / claims

The paper's central evidence is in **Table 1**. The two headline claims:

- **Without LLM assistance**, Chompy's rules subsume up to 71.1% of the
  handwritten Caviar ruleset (the `baseline` row of Table 1).
- **With LLM-guided filtering**, Chompy's ruleset shrinks by up to 44.3%
  while losing as little as 4.5% derivability (the `llm_filter_top_5` row).

Five independent runs of all seven configurations are shipped under
`eval-paper/` (35 cells total). The canonical numerical summary is in
`expected_results.csv` at the repo root.

## Installation

The reproduction path is **Docker**. The shipped `Dockerfile` builds Ubuntu
22.04 + Z3 4.12.1 (from source — this is the Z3 version `z3-sys 0.8.1`
bundles, and the version that produced the paper's numbers) + Rust + a
release build of Chompy. First-time build is ~15-20 min and is cached
afterwards.

```bash
docker build -t chompy:latest .
```

A direct (non-Docker) build also works on macOS and Ubuntu, but uses
whatever Z3 your system provides — currently Homebrew Z3 4.15.4 on macOS,
which produces a *slightly* different ruleset than the paper. For
byte-identical reproduction, use Docker.

```bash
# Optional: native build, for development. Not used by the reproduction steps.
cargo build --release
```

## Reproducing Table 1

We provide four ways to verify Table 1, ordered cheapest to most thorough.
Each step trusts strictly more than the previous one:

| # | Step                                       | Tool             | Wall clock      | Trusts |
|---|--------------------------------------------|------------------|-----------------|--------|
| 1 | Kick the tires                             | local cargo      | ~1 min          | binary works at all |
| 2 | Recreate Table 1 from shipped JSONs        | python only      | ~5 s            | the shipped JSONs |
| 3 | Verify the baseline binary                 | Docker           | ~25 min         | the shipped Docker |
| 4 | Re-derive Table 1 from shipped rulesets    | Docker           | ~30-60 min      | nothing — re-runs derivability from scratch |

You don't have to do all four. Step 2 alone reproduces the paper's numbers
from the shipped data; later steps progressively widen what's actually being
verified.

### Step 1 — Kick the tires (~1 min)

Sanity-check that the Chompy binary builds and runs on your machine. This
runs a small "mini" recipe and checks the rule count.

```bash
python3 python/kick_the_tires.py
```

You should see `mini.txt contains 57 rules ✅`. Outputs land in
`mini-artifacts/`.

### Step 2 — Recreate Table 1 from shipped JSONs (~5 s, no Docker)

The shipped artifact already contains every derivability JSON used to
populate Table 1. Recreating the table is a pure Python summation over
those files:

```bash
python3 python/summarize_runs.py eval-paper expected_results.csv
```

The output should match `expected_results.csv` exactly:

```
row                       n_runs  num_rules      caviar_derivability  halide_derivability  runtime_seconds
baseline                  5       1579.0 ± 0.0   73.3 ± 0.0           57.1 ± 0.0           1551.7 ± 13.9
llm_only                  5       116.4 ± 11.5   9.8 ± 5.8            3.1 ± 2.5            30.7 ± 3.4
llm_with_enum             5       1526.4 ± 20.0  73.3 ± 0.0           58.3 ± 1.2           1676.0 ± 47.3
llm_filter_top_1          5       882.6 ± 22.3   66.2 ± 3.7           55.5 ± 2.6           2176.5 ± 57.5
llm_filter_top_5          5       1430.0 ± 15.8  71.1 ± 2.2           59.8 ± 2.4           2269.0 ± 140.3
only_llm_terms            5       207.6 ± 18.5   25.8 ± 10.3          14.8 ± 12.6          551.9 ± 41.5
llm_terms_and_llm_filter  5       1403.4 ± 61.7  73.3 ± 1.6           60.0 ± 1.4           2333.8 ± 139.5
```

This is what Table 1 reports (with display-name renaming — see the
provenance map below).

### Step 3 — Verify the baseline binary (~25 min, Docker)

Re-synthesize the deterministic `baseline` row from scratch in Docker. No
LLM is involved, so the output is reproducible byte-for-byte:

```bash
mkdir -p eval-docker
docker run --rm -v "$(pwd)/eval-docker:/output" chompy:latest \
    /chompy/target/release/ruler \
    --recipe full --llm-usage baseline \
    --output-path /output/docker_baseline.txt
```

`docker_baseline.txt` should contain **1579 rules** and be byte-identical
(when sorted) to any of the five shipped baselines, e.g.
`eval-paper/run_1/full/baseline/full_baseline.txt`. Derivability matches
Table 1 exactly: 71.1% Caviar, 57.1% Halide.

### Step 4 — Re-derive Table 1 from shipped rulesets (~30-60 min, Docker)

The strongest verification. `reproduce.py` does NOT trust the shipped
JSONs — it re-runs derivability against every shipped ruleset from scratch
in Docker:

```bash
python3 reproduce.py
```

Mechanically, it:

1. Mirrors `eval-paper/` to `eval-paper-rerun/` (only `.txt` and `.log`
   files; the shipped JSONs are *not* copied).
2. Runs `--derive-only` against each of the 35 rulesets in the rerun tree,
   producing fresh `*_against_caviar.json` and `*_against_halide.json`
   files there.
3. Summarizes the rerun into `results.csv`.
4. Prints a side-by-side comparison of `expected_results.csv` (shipped)
   vs. `results.csv` (just-produced) with per-cell tolerance bands.

Per-cell drift of ≤ 1 percentage point on derivability and ≤ 5 rules on
rule counts is **expected** (Z3 has minor solver nondeterminism, and a
small number of borderline implications can flip between `can` and
`cannot` buckets across runs). Larger drift suggests either a Z3 version
mismatch or a hardware-related timeout that cut work short.

The shipped `eval-paper/` is never modified by `reproduce.py`. You can
re-run the script as many times as you like; each run lands in
`eval-paper-rerun/` (gitignored).

## File layout / provenance map

Within `eval-paper/`, the layout is `eval-paper/run_N/full/<llm-usage>/`,
where `N` is 1..5 (independent re-runs that we average to get Table 1's
mean ± stddev cells) and `<llm-usage>` is the CLI flag that produced that
cell. Each `<llm-usage>/` subfolder contains four files:

- `full_<usage>.txt` — the synthesized ruleset
- `full_<usage>.log` — Chompy's run log (used to extract synthesis
  runtime via the line `finished recipe (seconds: ...)`)
- `full_<usage>_against_caviar.json` — forwards/backwards derivability
  against the Caviar handwritten ruleset
- `full_<usage>_against_halide.json` — same, against Halide

The CLI flag → Table 1 row mapping:

| Paper row (Table 1)         | CLI `--llm-usage`                  | What the LLM does |
|-----------------------------|------------------------------------|-------------------|
| `baseline`                  | `baseline`                         | nothing — no LLM is called |
| `llm_only`                  | `llm_only`                         | LLM proposes whole rules; Chompy is bypassed; rules kept iff syntactically and semantically (Z3) valid |
| `llm_with_enum`             | `baseline_and_enum`                | LLM appends 40 terms per call site; conditions still come from Chompy only |
| `llm_filter_top_1`          | `baseline_and_filter_1`            | Chompy enumerates as in baseline; if a candidate set has > 10 rules, LLM clusters them and keeps the top 1 per cluster |
| `llm_filter_top_5`          | `baseline_and_filter_5`            | Same, top 5 per cluster |
| `only_llm_terms`            | `enum_only`                        | Both terms and conditions come exclusively from the LLM |
| `llm_terms_and_llm_filter`  | `baseline_with_filter_5_and_enum`  | `llm_with_enum` + `llm_filter_top_5` filtering |

The Halide-derivability denominator is fixed at 84 (the original Halide
test set has 112 rules, but 28 of those use `select`, which Chompy's
target Halide language doesn't include; these are excluded from the
denominator).

## Optional — Full LLM-driven re-synthesis

Steps 1–4 verify that the *shipped* rulesets reproduce Table 1. To verify
that the rulesets themselves were produced honestly — i.e., to re-run the
LLM-in-the-loop synthesis pipeline that *generated* them — use:

```bash
export OPENAI_API_KEY=sk-...
python3 python/run_the_eval.py
```

This runs all seven LLM-usage configurations once, lands outputs under a
fresh `eval/<timestamp>/full/<mode>/` tree, and takes about an hour.

Because the LLM is non-deterministic by design, the resulting rulesets
will *not* be bit-identical to the shipped ones — only the `baseline` row
is deterministic. Expect rule counts within ~5% of the shipped means and
derivability within ~1pp.

If you don't have an OpenAI key, you can still inspect the shipped per-run
LLM outputs in `eval-paper/run_N/full/enum_only/llm_responses.jsonl` and
similar files.

## Reusability — extending Chompy

This section describes how to extend Chompy to discover conditional rules
for new domains.

### Project layout

Much of Chompy's code is inherited from Enumo, the theory exploration
work that precedes Chompy. The key files for the core algorithm:

- `src/recipe_utils.rs` — top-level rule-inference algorithm
  (`run_workload`).
- `src/llm.rs` — LLM enumeration and clustering helpers.
- `src/conditions/` — conditional rule synthesis.
  - `assumption.rs` — adding an assumption to an e-graph.
  - `implication.rs` — defining and applying implications.
  - `implication_set.rs` — synthesizing implication sets via pvec
    matching.
  - `manager.rs` — implication-lattice logic (uses `egglog` as a
    Datalog-style backend).

### Adding a new domain

Chompy inherits Enumo's `SynthLanguage` trait. A reference implementation
is in `src/halide.rs` (the `Pred` struct). Once a `SynthLanguage`
implementation is complete, `run_workload` from `recipe_utils.rs` can be
called to discover new rules.
