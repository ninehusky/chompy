#!/usr/bin/env python3
"""
Verify a Chompy baseline run's outputs against the shipped reference.

Usage:
    python3 python/verify_baseline.py <docker_baseline.txt>

Pass the path to the .txt ruleset produced by the Step 3 docker command.
The script infers the sibling JSON paths (<basename>_against_caviar.json
and <basename>_against_halide.json) and checks:

  1. Rule count == 1579 (the shipped baseline size).
  2. Caviar derivability is within 1pp of the shipped baseline mean
     (read from expected_results.csv at the repo root).
  3. Halide derivability is within 1pp of the shipped baseline mean.

Exits non-zero if any check fails.
"""
import csv
import json
import sys
from pathlib import Path

EXPECTED_RULES = 1579
EXPECTED_CSV = "expected_results.csv"
HALIDE_DENOMINATOR = 84
TOLERANCE_PP = 1.0


def parse_cell_mean(s: str) -> float:
    return float((s or "").split("±")[0].strip())


def shipped_baseline_pcts(repo_root: Path):
    """Return (caviar_pct, halide_pct) from the baseline row of the shipped CSV."""
    with open(repo_root / EXPECTED_CSV) as f:
        for row in csv.DictReader(f):
            if row["row"] == "baseline":
                return (
                    parse_cell_mean(row["caviar_derivability"]),
                    parse_cell_mean(row["halide_derivability"]),
                )
    raise RuntimeError(f"no `baseline` row in {EXPECTED_CSV}")


def derivability_counts(json_path: Path, fixed_denom=None):
    """Return (can, denom) from the forwards bucket of a derivability JSON."""
    with open(json_path) as f:
        data = json.load(f)
    fwd = data.get("forwards", {})
    can = len(fwd.get("can", []))
    denom = fixed_denom if fixed_denom else can + len(fwd.get("cannot", []))
    return can, denom


def main():
    if len(sys.argv) != 2:
        print(__doc__, file=sys.stderr)
        sys.exit(1)

    txt_path = Path(sys.argv[1]).resolve()
    if txt_path.suffix != ".txt" or not txt_path.exists():
        print(f"ERROR: {txt_path} is not a readable .txt file", file=sys.stderr)
        sys.exit(1)

    caviar_json = txt_path.with_name(txt_path.stem + "_against_caviar.json")
    halide_json = txt_path.with_name(txt_path.stem + "_against_halide.json")
    for j in (caviar_json, halide_json):
        if not j.exists():
            print(f"ERROR: expected {j} alongside the ruleset; not found.", file=sys.stderr)
            sys.exit(1)

    repo_root = Path(__file__).resolve().parent.parent
    expected_caviar, expected_halide = shipped_baseline_pcts(repo_root)

    failed = False

    print(f"Checking ruleset size of {txt_path}...")
    with open(txt_path) as f:
        actual_rules = sum(1 for _ in f)
    if actual_rules == EXPECTED_RULES:
        print(f"Matches {EXPECTED_RULES}!")
    else:
        print(f"Got {actual_rules} rules, expected {EXPECTED_RULES}. Mismatch.")
        failed = True
    print()

    print(f"Checking derivability metrics of {halide_json}...")
    can_h, denom_h = derivability_counts(halide_json, fixed_denom=HALIDE_DENOMINATOR)
    pct_h = (can_h / denom_h) * 100 if denom_h else 0.0
    delta_h = abs(pct_h - expected_halide)
    verdict_h = (
        f"Matches shipped {expected_halide:.1f}% (±{TOLERANCE_PP:g}pp)!"
        if delta_h <= TOLERANCE_PP
        else f"drift {delta_h:.2f}pp > {TOLERANCE_PP:g}pp tolerance vs shipped {expected_halide:.1f}%."
    )
    print(f"derives {can_h} / {denom_h} rules -- {pct_h:.1f}%. {verdict_h}")
    if delta_h > TOLERANCE_PP:
        failed = True
    print()

    print(f"Checking derivability metrics of {caviar_json}...")
    can_c, denom_c = derivability_counts(caviar_json)
    pct_c = (can_c / denom_c) * 100 if denom_c else 0.0
    delta_c = abs(pct_c - expected_caviar)
    verdict_c = (
        f"Matches shipped {expected_caviar:.1f}% (±{TOLERANCE_PP:g}pp)!"

        if delta_c <= TOLERANCE_PP
        else f"drift {delta_c:.2f}pp > {TOLERANCE_PP:g}pp tolerance vs shipped {expected_caviar:.1f}%."
    )
    print(f"derives {can_c} / {denom_c} rules -- {pct_c:.1f}%. {verdict_c}")
    if delta_c > TOLERANCE_PP:
        failed = True

    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
