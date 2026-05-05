#!/usr/bin/env bash
# Targeted retry: keep running enum_only on the specific run dirs that
# don't yet have enum_only data, until they succeed (or we hit the cap).
# Each retry is just enum_only standalone (~10 min on success, ~3 min on OOM).
set -uo pipefail
cd "$(dirname "$0")/.."

if [[ -z "${OPENAI_API_KEY:-}" ]]; then
    echo "FATAL: OPENAI_API_KEY not set" >&2
    exit 1
fi

ts() { date "+%Y-%m-%d %H:%M:%S"; }
log() { echo "[retry $(ts)] $*"; }

MAX_ATTEMPTS_PER_DIR="${MAX_ATTEMPTS_PER_DIR:-6}"

is_complete() {
    local d="$1"
    local txt="$d/full/enum_only/full_enum_only.txt"
    local cav="$d/full/enum_only/full_enum_only_against_caviar.json"
    local hal="$d/full/enum_only/full_enum_only_against_halide.json"
    [[ -s "$txt" && -f "$cav" && -f "$hal" ]]
}

for run_dir in eval-docker/*/; do
    [[ -d "$run_dir" ]] || continue
    if is_complete "$run_dir"; then
        log "$(basename "$run_dir"): enum_only already OK, skipping"
        continue
    fi

    log "$(basename "$run_dir"): retrying enum_only up to $MAX_ATTEMPTS_PER_DIR times"

    for attempt in $(seq 1 $MAX_ATTEMPTS_PER_DIR); do
        if is_complete "$run_dir"; then
            log "$(basename "$run_dir"): enum_only OK after $((attempt-1)) retry"
            break
        fi
        log "$(basename "$run_dir"): attempt $attempt/$MAX_ATTEMPTS_PER_DIR"

        mode_dir="$run_dir/full/enum_only"
        mkdir -p "$mode_dir"
        rm -f "$mode_dir"/*.txt "$mode_dir"/*.json "$mode_dir"/*.jsonl

        docker run --rm \
            -v "$(pwd)/eval-docker:/chompy/eval-docker" \
            -v "$(pwd)/llm_cached:/chompy/llm_cached" \
            -e OPENAI_API_KEY \
            -e CHOMPY_LLM_LOG_DIR="/chompy/$mode_dir" \
            chompy:latest \
            /chompy/target/release/ruler \
                --recipe full --llm-usage enum_only \
                --output-path "/chompy/$mode_dir/full_enum_only.txt" \
            > "$mode_dir/full_enum_only.log" 2>&1
        rc=$?
        if is_complete "$run_dir"; then
            log "$(basename "$run_dir"): SUCCESS on attempt $attempt"
            break
        else
            log "$(basename "$run_dir"): FAILED (exit $rc) on attempt $attempt; retrying"
        fi
    done

    if ! is_complete "$run_dir"; then
        log "$(basename "$run_dir"): GIVING UP after $MAX_ATTEMPTS_PER_DIR attempts"
    fi
done

log "all done."
