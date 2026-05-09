#!/usr/bin/env python3
"""
Kick the tires: synthesize a small Chompy ruleset (the "mini" recipe)
inside Docker and verify the binary produces the expected rule count.

Outputs land in ./mini-artifacts/. The Docker image (chompy:latest) is
built from the canonical Dockerfile if it does not already exist; the
first build is ~15-20 min, subsequent invocations take seconds.
"""
import os
import subprocess
import sys
from pathlib import Path

DOCKER_IMAGE = "chompy:latest"
EXPECTED_RULES = 57
TARGET_DIR = Path("mini-artifacts")


def image_exists(tag: str) -> bool:
    return subprocess.run(
        ["docker", "image", "inspect", tag],
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
    ).returncode == 0


def build_image(repo_root: Path):
    print(f"[kick_the_tires] Building {DOCKER_IMAGE} (first build is ~15-20 min)...")
    subprocess.run(
        ["docker", "build", "-t", DOCKER_IMAGE, "."],
        cwd=repo_root, check=True,
    )


def main():
    repo_root = Path(__file__).resolve().parent.parent
    target = (repo_root / TARGET_DIR).resolve()
    target.mkdir(parents=True, exist_ok=True)

    if not image_exists(DOCKER_IMAGE):
        build_image(repo_root)

    print(f"[kick_the_tires] Running mini recipe in {DOCKER_IMAGE}...")
    log_path = target / "mini.log"
    docker_cmd = [
        "docker", "run", "--rm",
        "-v", f"{target}:/output",
        DOCKER_IMAGE,
        "/chompy/target/release/ruler",
        "--recipe", "mini",
        "--llm-usage", "baseline",
        "--output-path", "/output/mini.txt",
    ]
    # On Linux/WSL, set --user so files created in the bind mount land owned
    # by the host user, not root. Docker Desktop on macOS does this mapping
    # automatically; this is harmless there too.
    if hasattr(os, "getuid"):
        docker_cmd.insert(3, "--user")
        docker_cmd.insert(4, f"{os.getuid()}:{os.getgid()}")

    with open(log_path, "w") as log:
        subprocess.run(docker_cmd, check=True, stdout=log, stderr=subprocess.STDOUT)

    ruleset = target / "mini.txt"
    if not ruleset.exists():
        print(f"ERROR: {ruleset} not found.", file=sys.stderr)
        sys.exit(1)
    with open(ruleset) as f:
        num_rules = sum(1 for _ in f)
    if num_rules != EXPECTED_RULES:
        print(
            f"ERROR: {ruleset} has {num_rules} rules, expected {EXPECTED_RULES}.",
            file=sys.stderr,
        )
        sys.exit(1)

    print(f"{ruleset.name} contains {num_rules} rules ✅")
    print(f"  artifacts in {target}/")


if __name__ == "__main__":
    main()
