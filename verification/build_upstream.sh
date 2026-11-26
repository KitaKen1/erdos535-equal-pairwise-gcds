#!/usr/bin/env bash
set -euo pipefail

minutes=$1
shift
mem_kib=$(awk '/^MemTotal:/ { print $2; exit }' /proc/meminfo)
memory_max=$((mem_kib * 1024 * 85 / 100))
memory_high=$((memory_max * 92 / 100))
echo "Reserving $((mem_kib / 1024 - memory_max / 1024 / 1024)) MiB outside the Lean build."

if [[ "$minutes" != 35m ]]; then
  (
    while true; do
      sleep 300 &
      timer=$!
      trap 'kill "$timer" 2>/dev/null || true; exit 0' TERM
      wait "$timer"
      ps -eo etimes=,rss=,comm=,args= | awk '$3 == "lean" {
        for (i = 4; i <= NF; i++) if ($i ~ /[.]lean$/) {
          printf "Active Lean source after %ss (%s KiB RSS): %s\n", $1, $2, $i
          break
        }
      }'
    done
  ) &
  observer=$!
  trap 'kill "$observer" 2>/dev/null || true' EXIT
fi

sudo -n systemd-run --wait --pipe --collect \
  --uid="$(id -u)" --gid="$(id -g)" --working-directory="$PWD" \
  --property="MemoryHigh=$memory_high" --property="MemoryMax=$memory_max" \
  --property=OOMPolicy=kill --property=Nice=10 \
  --setenv="HOME=$HOME" --setenv="PATH=$PATH" --setenv="LEAN_NUM_THREADS=$LEAN_NUM_THREADS" \
  --setenv="RUNNER_TRACKING_ID=${RUNNER_TRACKING_ID:-}" \
  /usr/bin/timeout --kill-after=30s "$minutes" "$HOME/.elan/bin/lake" build "$@"
