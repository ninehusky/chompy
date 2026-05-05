#!/usr/bin/env bash
# One-shot wrapper: tests enum_only at the current Docker memory cap (14 GB
# at the time of writing), then re-enables enum_only in the eval scripts if
# the test succeeds, then launches the babysitter detached.
#
# Designed to be the last thing you fire before going to sleep:
#
#     nohup bash python/postmortem.sh > /tmp/chompy_postmortem.log 2>&1 &
#     disown
#
# Even if Claude Code closes / the laptop drops out of caffeinate scope, this
# script runs to completion under nohup and the babysitter takes over from
# there.
set -uo pipefail
cd "$(dirname "$0")/.."

ts() { date "+%Y-%m-%d %H:%M:%S"; }
log() { echo "[postmortem $(ts)] $*"; }

if [[ -z "${OPENAI_API_KEY:-}" ]]; then
    log "FATAL: OPENAI_API_KEY not set"
    exit 1
fi

RUN_DIR="eval-docker/2026_05_03_03_22"
ENUM_DIR="$RUN_DIR/full/enum_only"
ENUM_TXT="$ENUM_DIR/full_enum_only.txt"
ENUM_CAV="$ENUM_DIR/full_enum_only_against_caviar.json"
ENUM_HAL="$ENUM_DIR/full_enum_only_against_halide.json"
ENUM_LOG="$ENUM_DIR/full_enum_only.log"

# Step 1: standalone enum_only test at the current memory cap.
log "starting standalone enum_only test (cap = $(docker info --format '{{.MemTotal}}' | awk '{printf "%.2f GiB", $1/1024/1024/1024}'))"
mkdir -p "$ENUM_DIR"
rm -f "$ENUM_DIR"/*.txt "$ENUM_DIR"/*.json "$ENUM_DIR"/*.jsonl

docker run --rm \
    -v "$(pwd)/eval-docker:/chompy/eval-docker" \
    -v "$(pwd)/llm_cached:/chompy/llm_cached" \
    -e OPENAI_API_KEY \
    -e CHOMPY_LLM_LOG_DIR="/chompy/$ENUM_DIR" \
    chompy:latest \
    /chompy/target/release/ruler \
        --recipe full --llm-usage enum_only \
        --output-path "/chompy/$ENUM_TXT" \
    > "$ENUM_LOG" 2>&1
TEST_RC=$?
log "enum_only standalone exited rc=$TEST_RC"

# Step 2: decide based on result.
if [[ -s "$ENUM_TXT" && -f "$ENUM_CAV" && -f "$ENUM_HAL" ]]; then
    log "enum_only SUCCESS — re-enabling in babysitter + run_the_eval scripts"

    # Re-add enum_only to MODES in run_overnight.sh (whole line replacement).
    sed -i.postmortem-bak \
        's|^MODES="${MODES:-.*}"$|MODES="${MODES:-baseline llm_only enum_only baseline_and_enum baseline_and_filter_1 baseline_and_filter_5 baseline_with_filter_5_and_enum}"|' \
        python/run_overnight.sh

    # Re-add enum_only to usages in run_the_eval.py (insert between llm_only
    # and baseline_and_enum, removing the comment lines if they exist).
    python3 <<'PY'
import re
p = 'python/run_the_eval.py'
with open(p) as f: s = f.read()
new = re.sub(
    r'    "llm_only",\n(    # enum_only excluded.*?\n    # Add back once memory issue is investigated\.\n)?    "baseline_and_enum",',
    '    "llm_only",\n    "enum_only",\n    "baseline_and_enum",',
    s,
    flags=re.DOTALL,
)
with open(p, 'w') as f: f.write(new)
PY
else
    log "enum_only FAIL (likely OOM) — leaving disabled in babysitter + scripts"
fi

# Step 3: launch the babysitter detached.
log "launching babysitter..."
> /tmp/chompy_overnight.log
nohup bash python/run_overnight.sh > /tmp/chompy_overnight.log 2>&1 &
BABY_PID=$!
disown
log "babysitter PID: $BABY_PID"
log "DONE."
