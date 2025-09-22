# Conditional Rewrite Rule Synthesis Using E-Graphs and LLMs

This is the artifact for our paper "Conditional Rewrite Rule Synthesis Using E-Graphs and LLMs".
In our paper, we discuss an extension to theory explorers that allow for (1) conditional
rule synthesis, and (2) LLM-guided theory exploration.

- Available: The artifact is available on Zenodo.
- Functional: Below we provide instructions for setting up the artifact. Then, we list the claims
  in the paper and provide instructions for how to recreate each claim.
- Reusable: Finally, we provide instructions for extending Chompy. These instructions describe
  how to set up Enumo on a different machine, modify the code, and extend it to
  find rewrites for new domains.
  

## Overview

This artifact allows for the reconstruction of the following claims:

**How powerful are Chompy's rules?** 
- Without LLM assistance, Chompy's rules subsume up to 71.1% of handwritten rules, as seen in the
  `baseline` row of `Table 1`.

**How do LLMs impact ruleset quality?** 
- Using LLMs to guide Chompy's filtering mechanism, Chompy's ruleset size decreases by up to
  44.3%
  with a decrease in derivability of as little as 4.5%, as shown in the `filter_5` row of `Table 1`.
  
  
## Installation

We have verified that the instructions and runtimes below are correct for machines
running MacOS. In particular, we have tested this using a MacBook with an M3 chip and 18 GB
of RAM, and an M2 chip with 96 GB of RAM.

If you wish to install Chompy on a machine running Ubuntu, the following commands should suffice
(although we do recommend using MacOS with the hardware above for best performance).


``` bash
apt update
apt install -y git
apt install -y curl
curl --proto '=https --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y'
source $HOME/.cargo/env
apt install -y build-essential
apt install -y libssl-dev pkg-config
apt install -y cmake
apt install -y python3
apt install -y clang libclang-dev
git clone https://github.com/ninehusky/chompy.git
cd chompy/
cargo build --release
```

## Verify Original Experiments (1 minute)

The original data used to create `Table 1` is included inside the `original-eval/` folder.
`Table 1` of the paper contains Chompy's performance across LLM settings, averaged
across three runs. Each run, e.g., `run_one`, contains the results of running Chompy
with 6 different LLM configurations, each lining up with a row in `Table 1`.

To quickly see a summary of these results, from
Chompy's root directory, run:

``` c
python3 summarize_original_eval.py original-eval original_summary.csv
```

`original_summary.csv` should match:

```
run_type,num_rules,caviar_derivability,halide_derivability,runtime_seconds
enum_only,169.0,5.2,0.8,220.7
filter_1,628.3,57.8,51.6,1939.3
with_enum,1684.3,68.1,56.7,1772.6
filter_5,877.7,68.1,61.5,1942.4
enum+filter,952.7,69.6,60.3,2086.0
baseline,1579.0,71.1,57.1,1549.3
```


The above csv shows the results used in the paper,
with two expected differences that do not affect the core findings:
-  Due to a rounding error, the `caviar_derivability` and `halide_derivability`
   values differ for `enum_only` and `with_enum`.
   The ruleset size for `enum+filter` also differs slightly for the same reason.
 - The `filter_5` row shows minor differences because one run of Chompy was accidentally
   ommitted from the original average due to a folder typo. This has been corrected, and
   the overall results are largely unchanged.

We now describe the file layout in more detail for the curious. In each LLM usage subfolder,
e.g., `original-eval/run_one/full/baseline_with_enum`,
there are four files:

- `<usage>.log`: a small snippet of the logs containing the runtime for that run.
- `<usage>.txt`: the final ruleset Chompy produced.
- `<usage>_against_caviar.json`: a file showing forwards derivability vs. the "Caviar" ruleset.
- `<usage>_against_halide.json`: a file showing forwards derivability vs. the "Halide" ruleset.

> [!NOTE]  
> This is a minor detail, whose result does not affect the validity of previous runs.
> The `against_halide.json` files have 24 additional Halide rules, but this is
> because the original file scrapers used for Chompy did not filter out the 28
> rules containing `select`.
> 
> Both the current version of Chompy and the `summarize_original_eval.py` script
> account for this adjustment, so the reported results from `summarize_original_eval`
> are consistent with what's in the paper.

## Kick The Tires (1 minute)

On a fresh machine, type:

```
python3 python/kick_the_tires.py
```

This should take about a minute. This runs a small version of Chompy on a "mini recipe",
and moves any files created into `mini-artifacts`. You'll know this step worked when the output
of the script included:

```
mini.txt contains 57 rules ✅
```

Another way of checking is to run `wc -l mini-artifacts/mini.txt`.

## Recreating Experiments (~1 hour)

### Running the evaluation

This section describes how to re-run the experiments we have in the paper, in particular
`Table 1`.

`python3 python/run_the_eval.py` produces one run of the experiments used to build up Table 1.
Chompy is able to be augmented with LLMs in different ways. The usages are:

```py
usages = [
    "baseline",
    "enum_only",
    "baseline_and_enum",
    "baseline_and_filter_1",
    "baseline_and_filter_5",
    "baseline_with_filter_5_and_enum",
]
```

Every usage besides `baseline` uses an LLM. Because LLMs are non-deterministic,
the results we reproduce in this section will not match up one-to-one with the previous results.
This is to be expected, and the `baseline` result can be used as a "ground truth" to compare
to the original results. The `baseline` results are unlikely to change across machines,
and if they do, it is expected they will change by very little.

For reproducibility and reviewer's convenience, we describe hwo to run the evaluation
without calling ChatGPT. We have cached OpenAI API calls in the `llm_cache` folder.
The files within `llm_cache` are named after the hash of an LLM request.
To use these cached results instead of ChatGPT, set the following environment
variable:

```
export FAKE_LLM="hehehe"
```

If you do wish to run with a paid ChatGPT API account, do not set this environment variable.
Instead, set an `OPENAI_API_KEY` environment variable accordingly. A full run of
`run_the_eval.py` (cached and not cached) takes about an hour, and if using ChatGPT,
costs about $3.00.


### Analyzing the results

Once `run_the_eval.py` has concluded, you can summarize the results by running
`python3 python/summarize.py eval/<your_dir> out.csv`.

Open `out.csv` to see the equivalent results of `Table 1`, adjusted for our new LLM calls.
It should match, or be close to, the following (with the exception of `runtime_seconds`,
which may differ between machines):

```
$ cat out.csv
run_type,num_rules,caviar_derivability,halide_derivability,runtime_seconds
baseline,1579,71.1,57.1,1939.4
enum_only,181,13.3,3.6,37.5
filter_1,653,57.8,54.8,1908.7
filter_5,910,66.7,61.9,1961.2
with_enum,970,68.9,60.7,1857.4
enum+filter,1574,71.1,57.1,1944.0
```


## Reusability

This section describes how to extend Chompy to find conditional rules for other domains.

### Project Layout

Much of Chompy's code is inherited from Enumo, the theory exploration work which
precedes Chompy. Here, we describe the key files which are used in Chompy's
core algorithm.

- The source code resides in the `src/` directory.
  - The main algorithm used for rule inference, `run_workload`, is located
    inside `recipe_utils.rs`
  - `llm.rs` contains the functions used to enumerate terms and semantically
     categorize existing rulesets.`
  - `conditions` defines much of the core structure and logic used
     to support conditional rule synthesis.
    - `assumption.rs` handles the logic responsible for adding an assumption
      to an egraph.
    - `implication.rs` defines an implication and implements the logic responsible
      for applying an implication to an e-graph.
    - `implication_set.rs` includes logic for synthesizing implication sets, including
       pvec matching.
    - `manager.rs` contains the logic for our implication lattice, which uses
      `egglog` as a Datalog-style backend.
      
### Extending Chompy to discover rules for a new domain

Chompy inherits Enumo's concept of a `SynthLanguage`, which is a Rust
trait that can be extended for different languages.
The example implementation for the Halide `SynthLanguage` can be seen in
`src/halide.rs` -- the `Pred` struct represents the Halide language.
Once a `SynthLanguage`'s implementation is complete,
the top level rule synthesis function, `run_workload`, can be called
to find new rules.




