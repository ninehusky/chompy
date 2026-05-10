#!/usr/bin/env python3
"""
Reproduce Chompy derivability numbers from the shipped rulesets.

The shipped artifact lives in ``eval-paper/`` and is the source of truth for
Table 1. This script does NOT modify it. Instead, it:

  1. Copies the .txt rulesets (and synthesis .log files) into a sibling
     ``eval-paper-rerun/`` tree.
  2. Runs ``--derive-only`` against each rulesets in the rerun tree, which
     writes fresh ``*_against_caviar.json`` and ``*_against_halide.json``
     files there.
  3. Summarizes the rerun into ``results.csv``.
  4. Prints a side-by-side comparison against the canonical
     ``expected_results.csv`` (summary of the shipped JSONs) with tolerance
     bands. Small per-cell drift is expected from Z3 solver nondeterminism.

Usage:
    python3 reproduce.py [--shipped-dir DIR] [--rerun-dir DIR]
                         [--expected-csv FILE] [--out FILE]
"""
import argparse
import csv
import os
import shutil
import subprocess
import sys
from pathlib import Path

DOCKER_IMAGE = "chompy:latest"
BINARY = "/chompy/target/release/ruler"

# Per-column tolerance for the rerun-vs-shipped comparison. Cells whose mean
# differs by more than the tolerance are flagged. Runtime is informational
# (the rerun's runtime column is just the original synthesis runtime carried
# over from the copied .log files), so it is never failed.
TOLERANCES = {
    "num_rules": 5.0,
    "caviar_derivability": 1.0,
    "halide_derivability": 1.0,
    "runtime_seconds": float("inf"),
}


def build_image(repo_root: Path):
    print(f"[reproduce] Building {DOCKER_IMAGE} (~15-20 min on first build, no-op afterwards)...")
    subprocess.run(
        ["docker", "build", "-t", DOCKER_IMAGE, "."],
        cwd=repo_root,
        check=True,
    )


def mirror_inputs(src: Path, dst: Path):
    if dst.exists():
        shutil.rmtree(dst)
    for f in src.rglob("*"):
        if not f.is_file() or f.suffix not in (".txt", ".log"):
            continue
        rel = f.relative_to(src)
        target = dst / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(f, target)


def run_derive_only(txt_path: Path, repo_root: Path):
    rel = txt_path.relative_to(repo_root)
    container_path = f"/repo/{rel}"
    print(f"[reproduce] --derive-only {rel}")
    user_args = []
    if hasattr(os, "getuid"):
        user_args = ["--user", f"{os.getuid()}:{os.getgid()}"]
    subprocess.run(
        [
            "docker", "run", "--rm", *user_args,
            "-v", f"{repo_root}:/repo",
            DOCKER_IMAGE,
            BINARY, "--derive-only", container_path,
        ],
        check=True,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )


def read_csv(path: Path):
    with open(path) as f:
        return list(csv.DictReader(f))


def parse_cell(s: str):
    s = (s or "").strip()
    if not s:
        return None
    return float(s.split("±")[0].strip())


def compare(expected: list, actual: list):
    by_act = {r["row"]: r for r in actual}
    cols = ("num_rules", "caviar_derivability", "halide_derivability", "runtime_seconds")
    header = f"{'row':28s} {'col':22s} {'expected':18s} {'actual':18s} {'Δ':>7s}  ok?"
    print(header)
    print("-" * len(header))
    failed = []
    for row in expected:
        name = row["row"]
        a = by_act.get(name)
        if a is None:
            print(f"{name:28s} (missing in rerun)")
            failed.append(name)
            continue
        for col in cols:
            em = parse_cell(row.get(col, ""))
            am = parse_cell(a.get(col, ""))
            if em is None or am is None:
                continue
            delta = am - em
            tol = TOLERANCES[col]
            ok = abs(delta) <= tol
            mark = "OK" if ok else "!!"
            print(f"{name:28s} {col:22s} {row[col]:18s} {a[col]:18s} {delta:+7.2f}  {mark}")
            if not ok:
                failed.append(f"{name}.{col}")
    print()
    if failed:
        print(f"[reproduce] {len(failed)} cell(s) outside tolerance: {failed}")
        print("[reproduce] Small drift here is expected (solver nondeterminism); large drift is not.")
    else:
        print("[reproduce] All cells within tolerance.")


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--shipped-dir", default="eval-paper")
    parser.add_argument("--rerun-dir", default="eval-paper-rerun")
    parser.add_argument("--expected-csv", default="expected_results.csv")
    parser.add_argument("--out", default="results.csv")
    args = parser.parse_args()

    repo_root = Path(__file__).parent.resolve()
    shipped = (repo_root / args.shipped_dir).resolve()
    rerun = (repo_root / args.rerun_dir).resolve()
    expected_csv = (repo_root / args.expected_csv).resolve()
    out_csv = (repo_root / args.out).resolve()

    if not shipped.is_dir():
        print(f"ERROR: {shipped} not found", file=sys.stderr)
        sys.exit(1)

    build_image(repo_root)

    print(f"[reproduce] Mirroring {shipped.name}/ -> {rerun.name}/ (.txt + .log only)...")
    mirror_inputs(shipped, rerun)

    txt_files = sorted(rerun.glob("*/full/*/*.txt"))
    if not txt_files:
        print(f"ERROR: no .txt rulesets found under {rerun}", file=sys.stderr)
        sys.exit(1)

    print(f"[reproduce] Found {len(txt_files)} rulesets - running derivability...")
    for txt in txt_files:
        run_derive_only(txt, repo_root)

    print(f"[reproduce] Summarizing -> {out_csv}")
    subprocess.run(
        ["python3", "python/summarize_runs.py", str(rerun), str(out_csv)],
        cwd=repo_root,
        check=True,
    )

    if expected_csv.exists():
        print(f"\n[reproduce] Comparing rerun against {expected_csv.name}:\n")
        compare(read_csv(expected_csv), read_csv(out_csv))
    else:
        print(f"\n[reproduce] ({expected_csv.name} not found - skipping comparison.)")

    print("\n[reproduce] Done.")


if __name__ == "__main__":
    main()
