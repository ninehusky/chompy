# Conditional Rewrite Rule Synthesis Using E-Graphs (FMCAD 2026 artifact)

This is the artifact for our FMCAD 2026 paper *"Conditional Rewrite Rule
Synthesis Using E-Graphs"*, which extends theory exploration to
support conditional rule synthesis.

The artifact targets the three FMCAD badges:

- **Available**
- **Functional** — every claim in the paper can be re-verified from this
  repository in a few minutes to a few hours, with steps ordered by trust
  (see *Reproducing Table 1* below).
- **Reusable** — Chompy can be extended to other domains via the
  `SynthLanguage` trait (see *Reusability* below).

## Overview / claims

The paper's central evidence is in **Table 1**. The headline
claim in the abstract: Chompy's rules subsume up to 73.3% of the
handwritten Caviar ruleset (the `baseline` row of Table 1).

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

## Reproducing Table 1

> **Note on conditional rule counts:** The published Table 1
> reports the number of *conditional* rules in each synthesized
> ruleset. This column is not part of `expected_results.csv` or the
> derivability pipeline — it is computed separately from the shipped `.txt`
> rulesets via Step 5 below.

We provide five ways to verify Table 1, ordered cheapest to most thorough.
Each step trusts strictly more than the previous one:

| # | Step                                       | Tool             | Wall clock      | Trusts |
|---|--------------------------------------------|------------------|-----------------|--------|
| 1 | Kick the tires                             | Docker           | ~1 min          | binary works at all |
| 2 | Recreate Table 1 from shipped JSONs        | python only      | ~5 s            | the shipped JSONs |
| 3 | Verify the baseline binary                 | Docker           | ~35 min         | the shipped Docker |
| 4 | Re-derive Table 1 from shipped rulesets    | Docker           | ~5 hours        | nothing — re-runs derivability from scratch |
| 5 | Count conditional rules                    | python only      | ~5 s            | the shipped `.txt` rulesets |


### Step 1 — Kick the tires (~1 min, Docker)

Sanity-check that the Chompy binary runs on your machine. This invokes
the `chompy:latest` image (built in *Installation* above) on a small
"mini" recipe and checks the rule count.

```bash
python3 python/kick_the_tires.py
```

You should see:
```bash
[kick_the_tires] Running mini recipe in chompy:latest...
mini.txt contains 57 rules ✅
  artifacts in your/path/to/chompy/mini-artifacts/
```

If you skipped the `docker build` step, this script will build the image
itself on first run (~15-20 min one-time).

### Step 2 — Recreate Table 1 from shipped JSONs (~5 s, no Docker)

The shipped artifact already contains every derivability JSON used to
populate Table 1. Recreating the table is a pure Python summation over
those files. Write the result to a scratch CSV, then diff it against the
canonical `expected_results.csv` (the shipped reference, which Step 4
compares against later — don't overwrite it):

```bash
python3 python/summarize_runs.py eval-paper /tmp/step2.csv
diff expected_results.csv /tmp/step2.csv
```

`diff` should produce no output (the two files are byte-identical). The
script also prints a human-readable table to stdout; after the
"Found 5 runs..." preamble, the table portion should look like this:

```
row                       n_runs  num_rules      caviar_derivability  halide_derivability  runtime_seconds
------------------------  ------  -------------  -------------------  -------------------  ---------------
baseline                  5       1579.0 ± 0.0   73.3 ± 0.0           57.1 ± 0.0           1551.7 ± 13.9
llm_only                  5       116.4 ± 11.5   9.8 ± 5.8            3.1 ± 2.5            30.7 ± 3.4
llm_with_enum             5       1526.4 ± 20.0  73.3 ± 0.0           58.3 ± 1.2           1676.0 ± 47.3
llm_filter_top_1          5       882.6 ± 22.3   66.2 ± 3.7           55.5 ± 2.6           2176.5 ± 57.5
llm_filter_top_5          5       1430.0 ± 15.8  71.1 ± 2.2           59.8 ± 2.4           2269.0 ± 140.3
only_llm_terms            5       207.6 ± 18.5   25.8 ± 10.3          14.8 ± 12.6          551.9 ± 41.5
llm_terms_and_llm_filter  5       1403.4 ± 61.7  73.3 ± 1.6           60.0 ± 1.4           2333.8 ± 139.5
```

This is what Table 1 reports (for clarity, in the paper we write `llm_terms_conds` for `only_llm_terms`
and for brevity, we write `llm_terms_filter` for `llm_terms_and_llm_filter`, and `llm_filter_k` for `llm_filter_top_k`).

### Step 3 — Verify the baseline binary (~35 min, Docker)

Re-synthesize the deterministic `baseline` row from scratch in Docker
(no LLM involved), then run `verify_baseline.py` on the output. The
docker command writes the ruleset and its derivability JSONs into
`eval-docker/`; the verify script checks the rule count and both
derivability numbers against the shipped reference in
`expected_results.csv`.

```bash
mkdir -p eval-docker
docker run --rm -v "$(pwd)/eval-docker:/output" chompy:latest \
    /chompy/target/release/ruler \
    --recipe full --llm-usage baseline \
    --output-path /output/docker_baseline.txt

python3 python/verify_baseline.py eval-docker/docker_baseline.txt
```

You should see:

```
Checking ruleset size of .../eval-docker/docker_baseline.txt...
Matches 1579!

Checking derivability metrics of .../eval-docker/docker_baseline_against_halide.json...
derives 48 / 84 rules -- 57.1%. Matches shipped 57.1% (±1pp)!

Checking derivability metrics of .../eval-docker/docker_baseline_against_caviar.json...
derives 33 / 45 rules -- 73.3%. Matches shipped 73.3% (±1pp)!
```

The script exits non-zero on any mismatch.

### Step 4 — Re-derive Table 1 from shipped rulesets (~5 hours, Docker)

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
mismatch or a hardware difference which impacts wall-clock
based timeouts.

The shipped `eval-paper/` is never modified by `reproduce.py`. You can
re-run the script as many times as you like; each run lands in
`eval-paper-rerun/`.

### Step 5 — Count conditional rules (~5 s, no Docker)

Counts the number of conditional rules (those with an `if` clause) in each
shipped ruleset, reporting mean ± stddev across the five runs. This is
computed directly from the `.txt` files and is independent of the
derivability pipeline:

```bash
python3 python/conditional_rule_counts.py eval-paper
```

You should see:

```
Found 5 run(s) in eval-paper

row                       n_runs  num_rules      num_conditional_rules
────────────────────────  ──────  ─────────────  ─────────────────────
baseline                  5       1579.0 ± 0.0   1174.0 ± 0.0
llm_only                  5       116.4 ± 11.5   40.0 ± 14.5
llm_with_enum             5       1526.4 ± 20.0  1118.8 ± 14.1
llm_filter_top_1          5       882.6 ± 22.3   477.6 ± 22.3
llm_filter_top_5          5       1430.0 ± 15.8  1025.0 ± 15.8
only_llm_terms            5       207.6 ± 18.5   117.0 ± 15.6
llm_terms_and_llm_filter  5       1403.4 ± 61.7  992.4 ± 59.0
```

(As a reminder, in the paper we write `llm_terms_conds` for `only_llm_terms`
`llm_terms_filter` for `llm_terms_and_llm_filter`, and `llm_filter_k` for `llm_filter_top_k`.)

For each row, the `num_conditional_rules` should match
what is reported in our paper's Table 1.

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

## Reusability — extending Chompy

This section describes how to extend Chompy to discover conditional rules
for new domains.

### Project layout

Much of Chompy's code is inherited from Enumo, the theory exploration
work that precedes Chompy. The key files for the core algorithm:

- `src/recipe_utils.rs` — top-level rule-inference algorithm
  (`run_workload`).
- `src/llm.rs` — LLM enumeration and clustering helpers. The prompts in the appendix are present here.
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
