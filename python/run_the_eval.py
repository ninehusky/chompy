#!/usr/bin/env python3
import os
import subprocess
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed

# Configurations
recipes = ["full"]
usages = [
    # 2026-05-04 (very late): focused batch — only the 3 LLM-enum modes,
    # which were previously blocked at 20/100 and now run at 40/40 (gpt-5.4).
    # The other 4 rows (baseline, llm_only, filter_1, filter_5) already have
    # n=5 in eval-docker/ from earlier runs and aren't affected by the
    # num_terms/num_conditions knobs.
    "enum_only",
    "baseline_and_enum",
    "baseline_with_filter_5_and_enum",
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
    # said in *this specific run*, separately from the canonical llm_cached/
    # which is shared across runs and overwritten on hash collision.
    env = {**os.environ, "CHOMPY_LLM_LOG_DIR": str(recipe_dir)}

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
