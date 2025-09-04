#!/usr/bin/env python3
import subprocess
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed

# Configurations
recipes = ["full"]
usages = [
    "baseline",
    "enum_only",
    "baseline_and_enum",
    "baseline_and_filter_1",
    "baseline_and_filter_5",
    "baseline_with_filter_5_and_enum",
]
out_dir = Path("out")
max_workers = 2  # run 2 at a time

def run_recipe(recipe: str, usage: str):
    # Directory for this recipe/usage
    recipe_dir = out_dir / recipe / usage
    recipe_dir.mkdir(parents=True, exist_ok=True)

    # Safe filenames
    safe_label = f"{recipe}_{usage}"
    output_txt = recipe_dir / f"{safe_label}.txt"
    output_log = recipe_dir / f"{safe_label}.log"

    print(f"🚀 Running {recipe}/{usage}")

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
