#!/usr/bin/env bash
set -euo pipefail

ROOT="${ROOT:-/home/aimama/aihub}"
HOL4="${HOL4:-$ROOT/CakeML/HOL4/bin/hol}"
MEGALODON="${MEGALODON:-$ROOT/repos/megalodon-1.13/bin/megalodon}"
MEGALODON_FILE="${MEGALODON_FILE:-$ROOT/Mettapedia/MettaKernel/Curriculum/Megalodon/01_basics.mg}"
KONTROLI_REPO="${KONTROLI_REPO:-$ROOT/repos/kontroli-rs}"
LOCAL_KOCHECK="${LOCAL_KOCHECK:-$KONTROLI_REPO/target/release/kocheck}"
DED_NAME="${DED_NAME:-}"
if [ -n "${DED_EXAMPLE:-}" ]; then
  DED_EXAMPLE="$DED_EXAMPLE"
elif [ -f "$KONTROLI_REPO/examples/nat.dk" ]; then
  DED_EXAMPLE="examples/nat.dk"
  DED_WORKDIR="${DED_WORKDIR:-$KONTROLI_REPO}"
else
  DED_EXAMPLE="$ROOT/repos/dedukti/examples/plus.dk"
fi
LOGDIR="${TRACE_LOG_DIR:-$PWD/.trace_itp_baselines.logs}"

mkdir -p "$LOGDIR"
LOGDIR="$(cd "$LOGDIR" && pwd)"

cleanup_logs() {
  if [ "${KEEP_TRACE_LOGS:-0}" != "1" ]; then
    rm -rf "$LOGDIR"
  fi
}
trap cleanup_logs EXIT

pick_dedukti() {
  if [ -n "$DED_NAME" ]; then
    command -v "$DED_NAME" || true
    return
  fi
  command -v dkcheck || command -v dk || command -v kocheck || {
    if [ -x "$LOCAL_KOCHECK" ]; then
      printf '%s\n' "$LOCAL_KOCHECK"
    fi
  } || true
}

run_trace() {
  local name="$1"
  shift
  local stdout="$LOGDIR/$name.stdout"
  local stderr="$LOGDIR/$name.stderr"
  local cwd="${TRACE_CWD:-}"
  echo "=== $name ==="
  set +e
  if [ -n "$cwd" ]; then
    (cd "$cwd" && /usr/bin/time -v timeout 30 "$@" >"$stdout" 2>"$stderr")
  else
    /usr/bin/time -v timeout 30 "$@" >"$stdout" 2>"$stderr"
  fi
  local status=$?
  set -e
  echo "status=$status"
  rg -n "User time|System time|Elapsed|Maximum resident|Exit status" "$stderr" || true
  if [ "$status" -ne 0 ]; then
    echo "--- stderr tail ---"
    tail -20 "$stderr"
    echo "--- stdout tail ---"
    tail -20 "$stdout"
  fi
}

if [ -x "$HOL4" ]; then
  HOL4_BIN="$HOL4" run_trace "HOL4-primitive-thm" bash -lc \
    'printf "%s\n" \
      "val th_refl = REFL ``T``;" \
      "val th_assume = ASSUME ``p:bool``;" \
      "val th_disch = DISCH ``p:bool`` th_assume;" \
      "val _ = print \"TRACE HOL4 primitive theorem object path\\n\";" \
      "val _ = OS.Process.exit OS.Process.success;" | "$HOL4_BIN"'
else
  echo "=== HOL4-primitive-thm ==="
  echo "SKIP: HOL4 executable not found at $HOL4"
fi

if [ -x "$MEGALODON" ] && [ -f "$MEGALODON_FILE" ]; then
  run_trace "Megalodon-small-kernel" "$MEGALODON" "$MEGALODON_FILE"
else
  echo "=== Megalodon-small-kernel ==="
  echo "SKIP: megalodon executable or example file not found"
fi

DED_BIN="$(pick_dedukti)"
DED_EXAMPLE_PATH="${DED_EXAMPLE}"
if [ -n "${DED_WORKDIR:-}" ] && [[ "$DED_EXAMPLE" != /* ]]; then
  DED_EXAMPLE_PATH="$DED_WORKDIR/$DED_EXAMPLE"
fi
if [ -n "$DED_BIN" ] && [ -f "$DED_EXAMPLE_PATH" ]; then
  TRACE_CWD="${DED_WORKDIR:-}" run_trace "Dedukti-or-Kontroli-example" "$DED_BIN" "$DED_EXAMPLE"
else
  echo "=== Dedukti-or-Kontroli-example ==="
  echo "SKIP: no dkcheck/dk/kocheck executable on PATH, or no example at $DED_EXAMPLE"
fi
