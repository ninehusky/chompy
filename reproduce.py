#!/usr/bin/env python3
"""
Reproduce Chompy derivability numbers from pre-generated rulesets.

Usage:
    python3 reproduce.py [--eval-dir EVAL_DIR] [--out CSV]

Finds every *.txt ruleset under EVAL_DIR (default: eval-paper/), runs
--derive-only on each using the chompy:derive-only Docker image, then
writes a summary CSV (default: results.csv).
"""
import argparse
import subprocess
import sys
from pathlib import Path

DOCKER_IMAGE = "chompy:derive-only"
BINARY = "/chompy/target/release/ruler"


def build_image(repo_root: Path):
    print("[reproduce] Building Docker image (no-op if unchanged)...")
    subprocess.run(
        ["docker", "build", "-t", DOCKER_IMAGE, "-f", "Dockerfile.update", "."],
        cwd=repo_root,
        check=True,
    )


def run_derive_only(txt_path: Path, repo_root: Path):
    rel = txt_path.relative_to(repo_root)
    container_path = f"/repo/{rel}"
    print(f"[reproduce] --derive-only {rel}")
    subprocess.run(
        [
            "docker", "run", "--rm",
            "-v", f"{repo_root}:/repo",
            DOCKER_IMAGE,
            BINARY, "--derive-only", container_path,
        ],
        check=True,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--eval-dir", default="eval-paper", help="Directory containing run_1..run_N")
    parser.add_argument("--out", default="results.csv", help="Output CSV path")
    args = parser.parse_args()

    repo_root = Path(__file__).parent.resolve()
    eval_dir = (repo_root / args.eval_dir).resolve()
    out_csv = Path(args.out).resolve()

    if not eval_dir.is_dir():
        print(f"ERROR: {eval_dir} not found", file=sys.stderr)
        sys.exit(1)

    build_image(repo_root)

    txt_files = sorted(eval_dir.glob("*/full/*/*.txt"))
    if not txt_files:
        print(f"ERROR: no .txt rulesets found under {eval_dir}", file=sys.stderr)
        sys.exit(1)

    print(f"[reproduce] Found {len(txt_files)} rulesets — running derivability...")
    for txt in txt_files:
        run_derive_only(txt, repo_root)

    print(f"[reproduce] Summarizing → {out_csv}")
    subprocess.run(
        ["python3", "python/summarize_runs.py", str(eval_dir), str(out_csv)],
        cwd=repo_root,
        check=True,
    )
    print("[reproduce] Done.")


if __name__ == "__main__":
    main()
