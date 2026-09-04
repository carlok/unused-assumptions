#!/bin/sh
# One sprint: a named store, a list of areas, every stage, resumable.
#
# Usage:  tools/sprint.sh <sprint-name> <area> [area ...]
# e.g.    tools/sprint.sh sprint-1 Order MeasureTheory Topology
#
# This exists alongside tools/sweep.sh rather than replacing it: the four
# completed areas were produced by that script and it stays as the record of
# how. Four things differ here, each paid for.
#
# 1. `caffeinate -i`. Idle sleep only, so the lid and the display behave
#    normally. Without it a four-day estimate becomes a fortnight of wall
#    clock, because the machine idles to sleep between the moments somebody
#    looks at it. The assertion lifts when this script exits.
#
# 2. No `| tail`. `tail` buffers its whole input, so piping a live stage
#    through it writes *nothing* to the log until the stage ends. A Tau Ceti
#    run looked dead for three hours that way while its database advanced
#    every few seconds. Stages write straight to the log, unbuffered
#    (`python3 -u`); read the summary from the file afterwards.
#
# 3. No `set -e` across areas. A stage that fails costs its own area and
#    nothing else, and says so in the log as a line carrying "failed": true.
#
# 4. Areas already finished are skipped, and the check is derived from the
#    database rather than from a marker file. A marker can disagree with the
#    data; a query cannot. The definition matches tools/note_tables.py: every
#    row decided, and the prior-art gate has run.
#
# GOTCHA: tools/status.py only reports the stores named in its own --db list.
# Starting a sprint on a new store without restarting the status runner leaves
# STATUS.md confidently stale about it -- it will keep describing the old
# sweeps and give no hint that anything else is running.

set -u

# Re-exec under caffeinate before doing anything, so the assertion covers the
# whole run and dies with it.
if [ "${SPRINT_CAFFEINATED:-0}" != "1" ]; then
  export SPRINT_CAFFEINATED=1
  exec caffeinate -i "$0" "$@"
fi

if [ "$#" -lt 2 ]; then
  echo "usage: $0 <sprint-name> <area> [area ...]" >&2
  exit 2
fi

SPRINT=$1
shift

# This script's own directory's parent: the repository root, wherever it was
# cloned. Nothing here may assume a path on one machine.
D=$(cd "$(dirname "$0")/.." && pwd)
# The Lean project whose Mathlib the sweep compiles against. Required: there is
# no sensible default, and guessing one produces a preflight failure that looks
# like a broken install.
LF=${SWEEP_REPO:?set SWEEP_REPO to a Lean project with Mathlib as a dependency}
DB=$D/scrutiny/$SPRINT.db
LOG=$D/runs/$SPRINT.log
cd "$D" || exit 1
mkdir -p "$D/runs" "$D/scrutiny"

log() {
  printf '%s\n' "$1" >> "$LOG"
}

now() {
  date -u +%H:%M:%SZ
}

# Complete means: rows exist for the area, none is undecided, and the gate has
# populated `subsumed` for at least one of them. Exit 0 when complete.
area_complete() {
  python3 - "$DB" "$1" <<'PY'
import sqlite3
import sys

database, area = sys.argv[1], sys.argv[2]
try:
    connection = sqlite3.connect(f"file:{database}?mode=ro", uri=True)
    columns = {c[1] for c in connection.execute("PRAGMA table_info(weakening)")}
    if "subsumed" not in columns:
        sys.exit(1)                      # gate has never run on this store
    rows = list(connection.execute(
        "SELECT verdict, subsumed FROM weakening WHERE module = ? OR module LIKE ?",
        (f"Mathlib.{area}", f"Mathlib.{area}.%")))
except sqlite3.Error:
    sys.exit(1)                          # no store yet, or no table yet
if not rows:
    sys.exit(1)
if any(verdict is None for verdict, _ in rows):
    sys.exit(1)
if not any(subsumed for _, subsumed in rows):
    sys.exit(1)
sys.exit(0)
PY
}

# run_stage <area> <name> <command...>
run_stage() {
  stage_area=$1
  stage_name=$2
  shift 2
  log "{\"area\": \"$stage_area\", \"stage\": \"$stage_name\", \"at\": \"$(now)\"}"
  if "$@" >> "$LOG" 2>&1; then
    return 0
  fi
  log "{\"area\": \"$stage_area\", \"stage\": \"$stage_name\", \"failed\": true, \"at\": \"$(now)\"}"
  return 1
}

# Three seconds against two days. A toolchain bump leaves the dependency's
# oleans unreadable ("incompatible header"), and `lake build` on the root
# package exits 0 without fixing them -- so every #check resolves nothing, the
# not_a_binder filter never runs, and every attempt returns `incoherent`. That
# store looks like a finished sweep and is worthless. It has happened twice.
# Fail loudly here instead.
preflight() {
  probe=$D/runs/.preflight.lean
  printf 'import Mathlib\n\n#check @Nat.succ_le_succ\n' > "$probe"
  if command -v timeout >/dev/null 2>&1; then limit="timeout 600"; else limit=""; fi
  out=$(cd "$LF" && $limit env -u LEAN_PATH lake env lean "$probe" 2>&1)
  rm -f "$probe"
  case "$out" in
    *"Nat.succ_le_succ :"*) return 0 ;;
  esac
  log "{\"sprint\": \"$SPRINT\", \"stage\": \"preflight\", \"failed\": true, \"at\": \"$(now)\"}"
  log "{\"detail\": \"$(printf '%s' "$out" | head -1 | tr -d '"\\\\')\"}"
  log "{\"hint\": \"run 'lake exe cache get' in $LF, then retry\"}"
  return 1
}

log "{\"sprint\": \"$SPRINT\", \"stage\": \"start\", \"areas\": \"$*\", \"at\": \"$(now)\"}"

if ! preflight; then
  echo "preflight failed; see $LOG" >&2
  exit 1
fi

for area in "$@"; do
  if area_complete "$area"; then
    log "{\"area\": \"$area\", \"stage\": \"skip\", \"reason\": \"already complete\", \"at\": \"$(now)\"}"
    continue
  fi

  run_stage "$area" collect \
    python3 -u tools/typeclass.py "$area" --repo "$LF" --db "$DB" --collect-only || continue
  run_stage "$area" signatures \
    python3 -u tools/signatures.py --repo "$LF" --db "$DB" --batch 150 --timeout 600 || continue
  run_stage "$area" precheck \
    python3 -u tools/precheck.py --repo "$LF" --db "$DB" --timeout 600 || continue
  run_stage "$area" attempt \
    python3 -u tools/typeclass.py "$area" --repo "$LF" --db "$DB" --timeout 300 || continue
  run_stage "$area" priorart \
    python3 -u tools/priorart.py --repo "$LF" --db "$DB" --timeout 300 || continue
  run_stage "$area" descent \
    python3 -u tools/floor.py --repo "$LF" --db "$DB" --timeout 300 || continue

  log "{\"area\": \"$area\", \"stage\": \"done\", \"at\": \"$(now)\"}"
done

log "{\"sprint\": \"$SPRINT\", \"stage\": \"complete\", \"at\": \"$(now)\"}"
