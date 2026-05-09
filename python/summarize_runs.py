#!/usr/bin/env python3
"""
Aggregate Chompy eval runs across multiple invocations of run_one_table.sh
into a single Table-1-style report with mean +/- stddev per cell.

Usage:
    python3 python/summarize_runs.py eval-docker [out.csv]

Each immediate subdirectory of EVAL_ROOT is treated as one run (the timestamped
dir produced by run_the_eval.py). Within each run, the script looks for the
seven canonical mode subdirs under <run>/full/<mode>/ and collects:
    - num_rules:           line count of *.txt
    - caviar_derivability: forwards.can / (forwards.can + forwards.cannot) * 100
    - halide_derivability: forwards.can / 84 * 100  (matches summarize_original_eval.py)
    - runtime_seconds:     parsed from "finished recipe (seconds: ...)" in *.log

Output is sorted in DISPLAY_ORDER and uses the renamed display labels.
"""
import csv
import json
import os
import statistics
import sys
from pathlib import Path

# Map --llm-usage flag (also the subdirectory name) -> Table 1 display name.
MODE_DISPLAY = {
    "baseline": "baseline",
    "llm_only": "llm_only",
    "enum_only": "only_llm_terms",
    "baseline_and_enum": "llm_with_enum",
    "baseline_and_filter_1": "llm_filter_top_1",
    "baseline_and_filter_5": "llm_filter_top_5",
    "baseline_with_filter_5_and_enum": "llm_terms_and_llm_filter",
}

# Display order matches the user's spec.
DISPLAY_ORDER = [
    "baseline",
    "llm_only",
    "llm_with_enum",
    "llm_filter_top_1",
    "llm_filter_top_5",
    "only_llm_terms",
    "llm_terms_and_llm_filter",
]

# Halide derivability uses a fixed denominator of 84 for parity with
# summarize_original_eval.py (the original scrapers included 28 select-using
# rules that were later filtered, leaving 84 canonical halide test rules).
HALIDE_DENOMINATOR = 84


def parse_runtime(log_path: Path):
    if not log_path.exists():
        return None
    with open(log_path) as f:
        for line in f:
            if "finished recipe (seconds:" in line:
                return float(line.split("seconds:")[1].split(")")[0])
    return None


def parse_forwards_ratio(json_path: Path, fixed_denominator=None):
    if not json_path.exists():
        return None
    with open(json_path) as f:
        data = json.load(f)
    fwd = data.get("forwards") or {}
    can = len(fwd.get("can", []))
    if fixed_denominator is not None:
        denom = fixed_denominator
    else:
        denom = can + len(fwd.get("cannot", []))
    if denom == 0:
        return None
    return (can / denom) * 100


def collect_run(run_dir: Path, mode_subdir: str):
    mode_dir = run_dir / "full" / mode_subdir
    if not mode_dir.is_dir():
        return None
    txt_files = sorted(mode_dir.glob("*.txt"))
    log_files = sorted(mode_dir.glob("*.log"))
    halide_jsons = sorted(mode_dir.glob("*_against_halide.json"))
    caviar_jsons = sorted(mode_dir.glob("*_against_caviar.json"))

    num_rules = None
    if txt_files:
        with open(txt_files[0]) as f:
            num_rules = sum(1 for _ in f)
    return {
        "num_rules": num_rules,
        "caviar": parse_forwards_ratio(caviar_jsons[0]) if caviar_jsons else None,
        "halide": parse_forwards_ratio(halide_jsons[0], fixed_denominator=HALIDE_DENOMINATOR) if halide_jsons else None,
        "runtime": parse_runtime(log_files[0]) if log_files else None,
    }


def fmt_cell(values, decimals=1):
    """Format mean +/- stddev. Returns '' if no values, '<v>' if just one."""
    vs = [v for v in values if v is not None]
    if not vs:
        return ""
    if len(vs) == 1:
        return f"{vs[0]:.{decimals}f}"
    return f"{statistics.mean(vs):.{decimals}f} ± {statistics.stdev(vs):.{decimals}f}"


def main():
    if len(sys.argv) < 2:
        print(__doc__, file=sys.stderr)
        sys.exit(1)
    root = Path(sys.argv[1])
    out_csv = sys.argv[2] if len(sys.argv) > 2 else None

    if not root.is_dir():
        print(f"ERROR: {root} is not a directory", file=sys.stderr)
        sys.exit(1)

    # Each immediate subdir of root containing a 'full/' is treated as one run.
    run_dirs = sorted(d for d in root.iterdir() if d.is_dir() and (d / "full").is_dir())
    if not run_dirs:
        print(f"ERROR: no runs found in {root} (looked for <subdir>/full/)", file=sys.stderr)
        sys.exit(1)

    print(f"Found {len(run_dirs)} run(s) in {root}:")
    for d in run_dirs:
        print(f"  - {d.name}")
    print()

    rows = []
    display_to_subdir = {v: k for k, v in MODE_DISPLAY.items()}
    for display_name in DISPLAY_ORDER:
        subdir = display_to_subdir.get(display_name)
        if subdir is None:
            continue

        n_rules, caviar, halide, runtime = [], [], [], []
        for run_dir in run_dirs:
            data = collect_run(run_dir, subdir)
            if data is None:
                continue
            # Only count this run as a data point if its .txt has rules AND
            # both derivability JSONs landed — a mode mid-flight will leave
            # an empty .txt (0 rules) and missing JSONs, which would otherwise
            # poison the mean/stddev.
            if data["num_rules"] is None or data["num_rules"] == 0:
                continue
            if data["caviar"] is None or data["halide"] is None:
                continue
            n_rules.append(data["num_rules"])
            caviar.append(data["caviar"])
            halide.append(data["halide"])
            if data["runtime"] is not None:
                runtime.append(data["runtime"])

        rows.append({
            "row": display_name,
            "n_runs": len(n_rules),
            "num_rules": fmt_cell(n_rules),
            "caviar_derivability": fmt_cell(caviar),
            "halide_derivability": fmt_cell(halide),
            "runtime_seconds": fmt_cell(runtime),
        })

    cols = ["row", "n_runs", "num_rules", "caviar_derivability", "halide_derivability", "runtime_seconds"]
    widths = {c: max(len(c), max((len(str(r[c])) for r in rows), default=0)) for c in cols}
    print("  ".join(c.ljust(widths[c]) for c in cols))
    print("  ".join("-" * widths[c] for c in cols))
    for r in rows:
        print("  ".join(str(r[c]).ljust(widths[c]) for c in cols))

    if out_csv:
        with open(out_csv, "w", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=cols)
            writer.writeheader()
            writer.writerows(rows)
        print(f"\nWrote {out_csv}")


if __name__ == "__main__":
    main()
