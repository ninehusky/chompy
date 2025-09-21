import os
import sys
import re
import csv
import json

def parse_runtime(log_file):
    with open(log_file) as f:
        for line in f:
            if "finished recipe (seconds:" in line:
                return float(line.split("seconds:")[1].split(")")[0].strip())
    return None

def count_rules(txt_file):
    with open(txt_file) as f:
        return sum(1 for _ in f)

def parse_derivability(json_file):
    with open(json_file) as f:
        data = json.load(f)
    forwards = data["forwards"]
    can = len(forwards["can"])
    total = can + len(forwards["cannot"])
    return can, total, (can / total * 100) if total > 0 else 0.0

def main():
    if len(sys.argv) < 2:
        print("Usage: python summarize.py EVAL_DIR [OUT_CSV]")
        sys.exit(1)

    eval_dir = sys.argv[1]
    out_csv = sys.argv[2] if len(sys.argv) > 2 else None

    run_types = [
        ("enum_only", "enum_only"),
        ("filter_1", "baseline_and_filter_1"),
        ("filter_5", "baseline_and_filter_5"),
        ("with_enum", "baseline_with_filter_5_and_enum"),
        ("enum+filter", "baseline_and_enum"),
    ]

    rows = []
    for run_name, dirname in run_types:
        run_dir = os.path.join(eval_dir, "full", dirname)

        # runtime
        runtime = None
        log_files = [f for f in os.listdir(run_dir) if f.endswith(".log")]
        if log_files:
            runtime = parse_runtime(os.path.join(run_dir, log_files[0]))

        # ruleset size
        num_rules = None
        txt_files = [f for f in os.listdir(run_dir) if f.endswith(".txt")]
        if txt_files:
            num_rules = count_rules(os.path.join(run_dir, txt_files[0]))

        # derivabilities
        halide_json = [f for f in os.listdir(run_dir) if f.endswith("_halide.json")]
        caviar_json = [f for f in os.listdir(run_dir) if f.endswith("_caviar.json")]

        halide = None
        caviar = None
        if halide_json:
            can, total, halide = parse_derivability(os.path.join(run_dir, halide_json[0]))
            print(f"{run_name}/halide: {can}/{total} ({halide:.2f}% derivable)")
        if caviar_json:
            can, total, caviar = parse_derivability(os.path.join(run_dir, caviar_json[0]))
            print(f"{run_name}/caviar: {can}/{total} ({caviar:.2f}% derivable)")

        rows.append([run_name, runtime, num_rules, halide, caviar])

    if out_csv:
        with open(out_csv, "w", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(["run_type", "runtime_seconds", "num_rules", "halide_derivability", "caviar_derivability"])
            writer.writerows(rows)
        print(f"\nWrote summary CSV to {out_csv}")

if __name__ == "__main__":
    main()
