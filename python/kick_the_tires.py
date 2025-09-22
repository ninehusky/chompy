import subprocess
import shutil
import os
import sys

# Step 1: run the cargo command and redirect output to mini.log
log_file = "mini.log"
print(f"Running cargo command, logging to {log_file}...")
with open(log_file, "w") as log:
    cmd = [
        "cargo", "run", "--release", "--bin", "ruler",
        "--", "--recipe", "mini", "--llm-usage", "baseline", "--output-path", "mini.txt"
    ]
    subprocess.run(cmd, check=True, stdout=log, stderr=subprocess.STDOUT)
print("Cargo run finished.")

# Step 2: check that mini.txt has 57 rules
mini_txt = "mini.txt"
expected_rules = 57

if not os.path.exists(mini_txt):
    print(f"Error: {mini_txt} not found!")
    sys.exit(1)

with open(mini_txt) as f:
    num_rules = sum(1 for _ in f)

if num_rules != expected_rules:
    print(f"Error: {mini.txt} has {num_rules} rules, expected {expected_rules}. Aborting move.")
    sys.exit(1)

print(f"{mini_txt} contains {num_rules} rules ✅")

# Step 3: make sure the target directory exists
target_dir = "mini-artifacts"
os.makedirs(target_dir, exist_ok=True)

# Step 4: move files
files_to_move = ["mini.txt", "mini_against_caviar.json", "mini_against_halide.json", log_file]
for f in files_to_move:
    if os.path.exists(f):
        shutil.move(f, os.path.join(target_dir, f))
        print(f"Moved {f} -> {target_dir}")
    else:
        print(f"Warning: {f} not found!")

print("All files moved successfully.")
