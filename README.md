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
  
We have verified that the instructions and runtimes
below are good with machines running MacOS with an M3 chip with 18 GB of RAM, and
an M2 chip with 96 GB of RAM.

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

To run Chompy using Docker, do the following:

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

## Verify Original Experiments (1 minute)

The original data used to create `Table 1` is included inside the `original-eval/` folder.
`Table 1` of the paper contains Chompy's performance across LLM settings, averaged
across three runs. Each run, e.g., `run_one`, contains the results of running Chompy
with 6 different LLM configurations, each lining up with a row in `Table 1`.

To quickly see a summary of these results, from
Chompy's root directory, run:

``` c
python3 summarize_original_eval.py og-out.csv
```

Opening `og-out.csv` will reveal the results used in the paper, with the exception of
two differences:
- Cells blah1 and blah2 are different because of a rounding error.
- Row `with_enum` has different numbers because of a folder name typo which
  caused that row to only contain the averages of 2 runs as opposed to 3.
  The numbers in the paper only differ by blah3.

We now describe the file layout in more detail for the curious. In each LLM usage subfolder,
e.g., `original-eval/run_one/full/baseline_with_enum`,
there are four files:

- `<usage>.log`: the output Chompy produced while generating a ruleset.
- `<usage>.txt`: the final ruleset Chompy produced.
- `<usage>_against_caviar.json`: a file showing forwards derivability vs. the "Caviar" ruleset.
- `<usage>_against_halide.json`: a file showing forwards derivability vs. the "Halide" ruleset.

> [!NOTE]  
> The forwards derivability metric in each JSON file can be computed as  
> 
> ```
> json["forwards"]["can"] / (json["forwards"]["can"] + json["forwards"]["cannot"])
> ```
> 
> In the original runs included with the respository,
> the denominators in the `_against_halide` JSONs correspond to 112 rules,
> whereas the paper reports results over 84 rules.  
> 
> This discrepancy arises because the original Halide ruleset contained 112 rules,
> but 28 of them involved the `select` operator, which Chompy does not support.
> We therefore excluded these 28 rules, leaving a denominator of 84.  
> 
> Both the current version of Chompy and the `summarize_original_eval.py` script
> account for this adjustment, so the reported results are consistent.

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

This section describes how to re-run the experiments we have in the paper, in particular
`Table 1`.

`python3/run_the_eval.py` produces one run of the experiments used to build up Table 1.
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

Any configuration besides `baseline` requires the usage of an `OPENAI_API_KEY` environment variable,
hooked up to an OpenAI account with enough credits. With real LLM calls,
a full run of `run_the_eval.py` takes about an hour and costs about $3.00.

For reproducibility and reviewer's convenience, we have allowed the option to
run the evaluation without actually calling ChatGPT. We have cached several
OpenAI API calls, which are stored in `llm_cache/`. The names of the files within
that directory are a hash of the LLM request. To use these cached results instead
of ChatGPT, do the following before you run:


``` c
export FAKE_LLM="hehehe"
```

Take note! The cached OpenAI API calls are not those which are used in the paper, so the numbers
will not be exactly the same as `Table 1`. 

If you do wish to run using an LLM, do not have `FAKE_LLM` declared, and set `OPENAI_API_KEY`to your
account's.

Running the evaluation takes about an hour on a MacBook Pro with an M3 CPU and 18 GB of RAM.
   
For a quick peek at the runs from a glance, once
`run_the_eval.py` has concluded,
run `python3 python/summarize.py <eval/your_dir> out.csv`.
Open `out.csv` to see the equivalent results of `Table 1`, adjusted for our new LLM calls.

With cached LLM responses, you should see this as the result of `python3 python/summarize.py out.csv`:

```
$ cat out.csv
run_type,num_rules,caviar_derivability,halide_derivability,runtime_seconds
enum_only,181,13.3,3.6,31.9
filter_1,653,57.8,54.8,1587.3
filter_5,910,66.7,61.9,1559.4
with_enum,970,68.9,59.5,1545.2
enum+filter,1574,71.1,57.1,1562.0
```


## Reusability

TODO: here's our code structure:
`src/conditions/...`
`src/llm.rs`

Here, we explain how to extend Chompy to different domains.
You would change `x.rs` to generate conditional rules for blah, and then...



