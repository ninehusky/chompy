#!/usr/bin/env python3
"""
Report conditional rule counts (mean ± stdev across runs) from shipped .txt rulesets.

Usage:
    python3 python/conditional_rule_counts.py [eval-paper]

A rule is conditional if it contains ' if ' in the line.
This script is read-only with respect to the eval pipeline — it does not touch
expected_results.csv, summarize_runs.py, or any derivability JSONs.
"""
import statistics
import sys
from pathlib import Path

MODE_DISPLAY = {
    "baseline": "baseline",
    "llm_only": "llm_only",
    "enum_only": "only_llm_terms",
    "baseline_and_enum": "llm_with_enum",
    "baseline_and_filter_1": "llm_filter_top_1",
    "baseline_and_filter_5": "llm_filter_top_5",
    "baseline_with_filter_5_and_enum": "llm_terms_and_llm_filter",
}

DISPLAY_ORDER = [
    "baseline",
    "llm_only",
    "llm_with_enum",
    "llm_filter_top_1",
    "llm_filter_top_5",
    "only_llm_terms",
    "llm_terms_and_llm_filter",
]


def count_conditional(txt_path: Path):
    with open(txt_path) as f:
        lines = f.readlines()
    total = len(lines)
    conditional = sum(1 for l in lines if " if " in l)
    return total, conditional


def fmt(values, decimals=1):
    vs = [v for v in values if v is not None]
    if not vs:
        return ""
    if len(vs) == 1:
        return f"{vs[0]:.{decimals}f}"
    return f"{statistics.mean(vs):.{decimals}f} ± {statistics.stdev(vs):.{decimals}f}"


def main():
    root = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("eval-paper")
    if not root.is_dir():
        print(f"ERROR: {root} is not a directory", file=sys.stderr)
        sys.exit(1)

    run_dirs = sorted(d for d in root.iterdir() if d.is_dir() and (d / "full").is_dir())
    if not run_dirs:
        print(f"ERROR: no runs found in {root}", file=sys.stderr)
        sys.exit(1)

    print(f"Found {len(run_dirs)} run(s) in {root}\n")

    display_to_subdir = {v: k for k, v in MODE_DISPLAY.items()}
    rows = []
    for display_name in DISPLAY_ORDER:
        subdir = display_to_subdir[display_name]
        totals, conditionals = [], []
        for run_dir in run_dirs:
            txt_files = sorted((run_dir / "full" / subdir).glob("*.txt"))
            if not txt_files:
                continue
            total, conditional = count_conditional(txt_files[0])
            if total == 0:
                continue
            totals.append(total)
            conditionals.append(conditional)
        rows.append((display_name, str(len(totals)), fmt(totals), fmt(conditionals)))

    col_headers = ("row", "n_runs", "num_rules", "num_conditional_rules")
    widths = [max(len(h), max((len(r[i]) for r in rows), default=0))
              for i, h in enumerate(col_headers)]
    fmt_row = lambda r: "  ".join(str(r[i]).ljust(widths[i]) for i in range(len(col_headers)))
    print(fmt_row(col_headers))
    print(fmt_row(["─" * w for w in widths]))
    for row in rows:
        print(fmt_row(row))


if __name__ == "__main__":
    main()
