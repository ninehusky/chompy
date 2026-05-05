#!/usr/bin/env bash
# Overnight babysitter: makes sure we end up with 5 complete runs of the
# Table 1 evaluation in eval-docker/, regardless of whether Claude Code is
# still open or the laptop has slept.
#
# Run this under nohup + caffeinate so it survives Claude Code closure and
# blocks system sleep:
#
#     caffeinate -dis nohup bash python/run_overnight.sh \
#         > /tmp/chompy_overnight.log 2>&1 &
#     disown
#
# Behavior:
#   1. Wait for any in-flight chompy:latest container to finish (so we don't
#      step on a run already underway).
#   2. Inspect each existing eval-docker/<run>/ directory; if a mode is
#      missing its derivability JSONs (e.g. the OOM-killed enum_only in
#      run 1), re-run JUST that mode standalone, writing back into the same
#      run dir.
#   3. Loop run_one_table.sh until eval-docker/ contains TARGET_RUNS complete
#      runs (default 5).
#
# Env overrides (with defaults):
#   TARGET_RUNS=5         # how many complete runs we want total
#   MODES="baseline llm_only enum_only baseline_and_enum baseline_and_filter_1 \
#          baseline_and_filter_5 baseline_with_filter_5_and_enum"
set -uo pipefail
# Don't `set -e` — we explicitly want failures to be logged, not abort the loop.

cd "$(dirname "$0")/.."

TARGET_RUNS="${TARGET_RUNS:-5}"
# 2026-05-04 (very late) — focused batch: only the 3 LLM-enum modes, at
# 40/40 (num_conditions/num_terms) on gpt-5.4. The other 4 modes already
# have n=5 from earlier runs; this fills the missing rows.
MODES="${MODES:-enum_only baseline_and_enum baseline_with_filter_5_and_enum}"

if [[ -z "${OPENAI_API_KEY:-}" ]]; then
    echo "[overnight] FATAL: OPENAI_API_KEY not set" >&2
    exit 1
fi

ts() { date "+%Y-%m-%d %H:%M:%S"; }
log() { echo "[overnight $(ts)] $*"; }

# A run is "complete" if all 7 modes have a non-empty .txt and both JSONs.
is_run_complete() {
    local run_dir="$1"
    for mode in $MODES; do
        local mode_dir="$run_dir/full/$mode"
        local txt="$mode_dir/full_${mode}.txt"
        local cav="$mode_dir/full_${mode}_against_caviar.json"
        local hal="$mode_dir/full_${mode}_against_halide.json"
        [[ -s "$txt" && -f "$cav" && -f "$hal" ]] || return 1
    done
    return 0
}

count_complete_runs() {
    local n=0
    for d in eval-docker/*/; do
        [[ -d "$d" ]] || continue
        is_run_complete "$d" && n=$((n + 1))
    done
    echo "$n"
}

# Recover a single mode standalone (full container RAM) inside an existing
# run dir. Used to patch up partial runs (e.g. OOM-killed enum_only).
recover_mode() {
    local run_dir="$1"  # e.g. eval-docker/2026_05_03_03_22
    local mode="$2"     # e.g. enum_only
    local mode_dir="$run_dir/full/$mode"
    local txt_path="/chompy/$run_dir/full/$mode/full_${mode}.txt"
    local log_path="$mode_dir/full_${mode}.log"

    log "RECOVER: rerunning $mode standalone into $mode_dir"
    mkdir -p "$mode_dir"
    rm -f "$mode_dir"/*.txt "$mode_dir"/*.json "$mode_dir"/*.jsonl 2>/dev/null

    docker run --rm \
        -v "$(pwd)/eval-docker:/chompy/eval-docker" \
        -v "$(pwd)/llm_cached:/chompy/llm_cached" \
        -e OPENAI_API_KEY \
        -e CHOMPY_LLM_LOG_DIR="/chompy/$mode_dir" \
        chompy:latest \
        /chompy/target/release/ruler \
            --recipe full --llm-usage "$mode" \
            --output-path "$txt_path" \
        > "$log_path" 2>&1
    local rc=$?
    if [[ $rc -ne 0 ]]; then
        log "RECOVER: $mode FAILED (exit $rc) — see $log_path"
        return $rc
    fi
    log "RECOVER: $mode OK"
}

# 1. Wait for any in-flight chompy:latest container to finish.
log "starting; target = $TARGET_RUNS complete runs"
while docker ps --format '{{.Image}}' 2>/dev/null | grep -q '^chompy:latest$'; do
    log "in-flight chompy container detected; waiting 60s..."
    sleep 60
done
log "no in-flight chompy container"

# 2. Patch up partial runs (recover missing modes).
for run_dir in eval-docker/*/; do
    [[ -d "$run_dir" ]] || continue
    if is_run_complete "$run_dir"; then
        log "$(basename "$run_dir"): already complete"
        continue
    fi
    log "$(basename "$run_dir"): partial — checking missing modes"
    for mode in $MODES; do
        mode_dir="$run_dir/full/$mode"
        txt="$mode_dir/full_${mode}.txt"
        cav="$mode_dir/full_${mode}_against_caviar.json"
        hal="$mode_dir/full_${mode}_against_halide.json"
        if [[ -s "$txt" && -f "$cav" && -f "$hal" ]]; then
            continue  # already good
        fi
        recover_mode "$run_dir" "$mode" || log "$(basename "$run_dir")/$mode: recovery failed, continuing"
    done
done

# 3. Loop fresh runs until we have TARGET_RUNS complete.
while :; do
    n=$(count_complete_runs)
    log "current complete run count: $n / $TARGET_RUNS"
    if (( n >= TARGET_RUNS )); then
        log "target reached — exiting"
        break
    fi
    log "kicking off run #$((n + 1))..."
    if bash python/run_one_table.sh; then
        log "run_one_table.sh exit 0"
    else
        log "run_one_table.sh exit non-zero — likely a per-mode crash; will patch up next iteration"
    fi

    # Try to patch up the run we just did, in case a mode crashed.
    latest=$(ls -1t eval-docker/ 2>/dev/null | head -1)
    if [[ -n "$latest" ]]; then
        for mode in $MODES; do
            mode_dir="eval-docker/$latest/full/$mode"
            txt="$mode_dir/full_${mode}.txt"
            cav="$mode_dir/full_${mode}_against_caviar.json"
            hal="$mode_dir/full_${mode}_against_halide.json"
            [[ -s "$txt" && -f "$cav" && -f "$hal" ]] && continue
            log "$latest/$mode missing — recovering"
            recover_mode "eval-docker/$latest" "$mode" \
                || log "$latest/$mode recovery FAILED, continuing"
        done
    fi
done

log "DONE. Summary:"
python3 python/summarize_runs.py eval-docker /tmp/chompy_overnight_summary.csv 2>&1 | tail -30
log "summary CSV: /tmp/chompy_overnight_summary.csv"
