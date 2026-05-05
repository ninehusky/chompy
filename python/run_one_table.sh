#!/usr/bin/env bash
# Run one full table-pass (all 7 modes, one cargo invocation per mode) inside
# the chompy:latest Docker image (Z3 4.12.1, for paper reproducibility).
#
# Invoke this 5 times to accumulate runs for mean/stddev. Outputs land in
# ./eval-docker/<timestamp>/ on the host. Subsequent invocations write to
# fresh timestamped subdirs.
#
# The LLM cache is bind-mounted, so cache misses populate the host's
# llm_cached/ for reviewers to replay later. Each invocation hits the live
# OpenAI API (FAKE_LLM is intentionally unset), which gives real variance
# across runs. Last writer wins on hash collisions.
set -euo pipefail

cd "$(dirname "$0")/.."

if [[ -z "${OPENAI_API_KEY:-}" ]]; then
    echo "ERROR: OPENAI_API_KEY is required (used on cache miss)." >&2
    echo "Set it via: export OPENAI_API_KEY=sk-..." >&2
    exit 1
fi

if ! command -v docker >/dev/null 2>&1; then
    echo "ERROR: docker is not on PATH." >&2
    exit 1
fi

mkdir -p eval-docker llm_cached

echo "[run_one_table] Building chompy:latest (no-op if source unchanged)..."
# Dockerfile.update bases on the existing chompy:latest (Ubuntu 22.04 + Z3
# 4.12.1 + apt deps + cargo target cache) and only refreshes source +
# incremental cargo build — used when Docker Hub anonymous metadata fetches
# stall on the canonical FROM ubuntu:22.04. If Dockerfile.update is missing
# (fresh checkout), fall back to the canonical Dockerfile.
if [[ -f Dockerfile.update ]]; then
    docker build -t chompy:latest -f Dockerfile.update .
else
    docker build -t chompy:latest .
fi

echo "[run_one_table] Running all 7 modes inside Docker (Z3 4.12.1)..."
docker run --rm \
    -v "$(pwd)/eval-docker:/chompy/eval-docker" \
    -v "$(pwd)/llm_cached:/chompy/llm_cached" \
    -e OPENAI_API_KEY \
    -e CHOMPY_EVAL_ROOT=eval-docker \
    chompy:latest \
    python3 python/run_the_eval.py

latest_run="$(ls -1t eval-docker/ | head -1)"
echo "[run_one_table] Done. Run landed at: eval-docker/${latest_run}"
echo "[run_one_table] Summarize accumulated runs with: python3 python/summarize_runs.py eval-docker out.csv"
