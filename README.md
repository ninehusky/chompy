# Conditional Rewrite Rule Synthesis Using E-Graphs and LLMs

This is the artifact for our paper "Conditional Rewrite Rule Synthesis Using E-Graphs and LLMs".
In our paper, we discuss an extension to theory explorers that allow for (1) conditional
rewrite rule synthesis 

- Available: The artifact is available on Zenodo.
- Functional: Below we provide instructions for setting up the artifact. Then, we list the claims
  in the paper and provide instructions for how to recreate each claim.
- Reusable: Finally, we provide instructions for extending Chompy. These instructions describe
  how to set up Enumo on a different machine, modify the code, and extend it to
  find rewrites for new domains.

## Overview

Our paper makes three claims:

**How powerful are Chompy's rules?** 
- Without LLM assistance, Chompy's rules subsume up to 71.1% of handwritten rules, as seen in the
  `baseline` row of `Table 1`.

**How do LLMs impact ruleset quality?** 
- Using LLMs to guide Chompy's filtering mechanism, Chompy's ruleset size decreases by up to
  44.3%
  with a decrease in derivability of as little as 4.5%, as shown in the `filter_5` row of `Table 1`.

**How does our technique of implication propagation affect conditional rule synthesis?** 
- If Chompy does not use our technique of implication propagation, it runs for several hours --
  much longer than the baseline time. In this time, it discovers many more rules
  than the final output of Chompy, as described in `Section 4.3`.
  
  
  
## Installation

This is all experimented on MacOS, and a Docker image running Ubuntu.

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
cargo build
```

## Kick The Tires

On a fresh machine, type:

```
cargo run --release --bin ruler -- --recipe mini --llm-usage baseline --output-path mini.txt
```

This should take about a minute. The ruleset included inside
`mini.txt` should include 57 rules (i.e., `wc -l mini.txt` should
include 57 rules).

In addition to `mini.txt`, you should also find `mini_against_caviar.json` and `mini_against_halide.json`.

That should include `TODO`...

`eval/run_*` includes the `json` files. Go through them and `TODO`...


## Recreating Experiments

This section describes how to re-run the experiments we have in the paper.


### Table 1

`python3/run_the_eval.py` produces one run of the experiments used to build up Table 1.
Chompy is able to be augmented with LLMs in different ways, each of which are within:

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

Any configuration besides `baseline` requires the usage of an `OPENAI_API_KEY` environment variable,
hooked up to an OpenAI account with enough credits. For reproducibility and reviewer's convenience,
we have cached several OpenAI API calls, which we store in `llm_cache/`.

Importantly, the cached OpenAI API calls are not those which are used in the paper, so the numbers
will not be exactly the same as `Table 1`, but they should be close enough.
To use these cached API calls, do:

``` c
export FAKE_LLM="hehehe"
```
If you do wish to run using an LLM, do not have `FAKE_LLM` declared, and set `OPENAI_API_KEY`to your
account's. Running one run of the experiment costs `todo` dollars. 

Run one run of the experiments using `python3/run_the_eval.py`. 

Once the run has finished, `eval/<date>_<time>/full/<run_type>` will be populated with several files.
Each `run_type` will have four files associated with it:
1. A `.log` file containing the `stdout` messages Chompy outputs during that run.
2. A `.txt` file with Chompy's ruleset.
3. A `...against_caviar.json` containing Chompy's derivability performance against Caviar.
   The forward derivability metric is `len(can) / len(cannot)` for the `forwards` item
   in the `json`.
4. A `...against_halide.json` containing Chompy's derivability performance against Halide.
   The forward derivability metric is the same as above.
   
For a quick peek at the runs from a glance, run `python3 python/show_results.py`.

TODO: make `show_results.py` spit out a CSV, explain roughly what a workload is

### Table 2

Table 2 describes the different workloads added to Chompy's overall ruleset.

Run:

```
cargo run --release --bin ruler -- --recipe full --llm-usage baseline --output-path fullpath.txt > fulllog.log
python3 python/get_workload_stats.py fulllog.log
```

You should see:

```
rules added by workload:
find_base_implications: 20
and_comps: 126
simp_comps: 82
arith_basic: 84
mul_div_mod: 37
min_max: 13
min_max_add: 6
eq_simp_min: 7
eq_simp_max: 6
min_max_mul: 53
min_max_div: 410
lt_add_min: 341
lt_add_max: 394
total: 1579
```

### Sensitivity Study

This step should take several hours. In our paper, we contribute a new
technique called implication propagation which helps conditional
rewrite synthesis scale to large grammars. Our sensitivity study's main
claim is that Chompy does not terminate if this step is disabled.

To disable implication propagation, set the environment variable `NO_IMPLICATIONS` to any value.
The following should suffice:

```
export NO_IMPLICATIONS="goodluck"
cargo run --release --bin ruler -- --recipe mini --llm-usage baseline --output-path mini.txt
```

While Chompy runs, you should observe that after an hour, the workload
`min_max_mul` will still be running.

TODO: on a MacBook with <blah> GB of RAM, it did not terminate in 2 hours, which is our
threshold for stopping the process.


## Reusability

TODO: here's our code structure:
`src/conditions/...`
`src/llm.rs`

Here, we explain how to extend Chompy to different domains.
You would change `x.rs` to generate conditional rules for blah, and then...



