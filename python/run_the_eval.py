#!/usr/bin/env python3
import os
import subprocess
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed

# Configurations
recipes = ["full"]
usages = [
    # 2026-05-04 (later): single-mode test of the new llm_only single-prompt
    # path (recipe machinery bypassed in main.rs). The previously-archived
    # n=5 llm_only runs in eval-docker/2026_05_03_*/full/llm_only/ are
    # invalidated (hybrid LLM + baseline-chompy under the bug) and have been
    # moved to eval-archive/llm_only_pre_single_prompt_2026_05_04/. Expand
    # this list back out (and to n=5 invocations of run_one_table.sh) once
    # this single run is verified.
    "llm_only",
]

# Output root is overridable so the docker wrapper can land runs in a separate
# tree (e.g. eval-docker/) without colliding with native runs.
eval_root = os.environ.get("CHOMPY_EVAL_ROOT", "eval")
out_dir = Path(eval_root) / Path(__import__("datetime").datetime.now().strftime("%Y_%m_%d_%H_%M"))
max_workers = 1  # serial: one ruler at a time, full container RAM (avoid OOM)

def run_recipe(recipe: str, usage: str):
    # Directory for this recipe/usage
    recipe_dir = out_dir / recipe / usage
    recipe_dir.mkdir(parents=True, exist_ok=True)

    # Safe filenames
    safe_label = f"{recipe}_{usage}"
    output_txt = recipe_dir / f"{safe_label}.txt"
    output_log = recipe_dir / f"{safe_label}.log"

    print(f"🚀 Running {recipe}/{usage}")

    # Per-mode audit log of every LLM API response (Rust side appends to
    # $CHOMPY_LLM_LOG_DIR/llm_responses.jsonl). Lets us see what the model
    # said in *this specific run*.
    #
    # Per-(run, recipe, mode) cache dir (Rust reads CHOMPY_LLM_CACHE_DIR and
    # falls back to llm_cached/). Without this override, all runs share
    # llm_cached/ and last-writer-wins on hash collision — fatal for paper
    # variance runs because n=5 invocations on the same prompt would all
    # collapse to whatever response the last run got. With it, each run dir
    # is self-contained and FAKE_LLM=1-replayable independently.
    env = {
        **os.environ,
        "CHOMPY_LLM_LOG_DIR": str(recipe_dir),
        "CHOMPY_LLM_CACHE_DIR": str(recipe_dir / "llm_cached"),
    }

    # Invoke cargo run
    with open(output_log, "w") as log_file:
        result = subprocess.run(
            [
                "cargo", "run", "--release", "--bin", "ruler",
                "--",  # stop parsing cargo args
                "--recipe", recipe,
                "--llm-usage", usage,
                "--output-path", str(output_txt),
            ],
            stdout=log_file,
            stderr=subprocess.STDOUT,
            check=True,  # crash if command fails
            env=env,
        )

    print(f"✅ Finished {recipe}/{usage}")

def main():
    futures = []
    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        for recipe in recipes:
            for usage in usages:
                futures.append(executor.submit(run_recipe, recipe, usage))

        # Wait for all
        for future in as_completed(futures):
            try:
                future.result()
            except subprocess.CalledProcessError as e:
                print(f"❌ Recipe failed: {e}")
                raise e

    print("🎉 All runs finished.")

if __name__ == "__main__":
    main()
