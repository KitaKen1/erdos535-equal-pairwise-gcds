#!/usr/bin/env bash
set -euo pipefail

minutes=$1
shift
mem_kib=$(awk '/^MemTotal:/ { print $2; exit }' /proc/meminfo)
memory_percent=85
high_percent=92

if [[ "$minutes" != 35m ]]; then
  if command -v zramctl >/dev/null && sudo -n modprobe zram &&
      zram_device=$(sudo -n zramctl --find --size 24G); then
    if printf '%s\n' 4294967296 | sudo -n tee "/sys/block/${zram_device##*/}/mem_limit" >/dev/null &&
        sudo -n mkswap "$zram_device" && sudo -n swapon --priority 100 "$zram_device"; then
      memory_percent=65
      high_percent=97
      sudo -n sysctl -w vm.swappiness=180 || true
      echo "Enabled compressed swap on $zram_device."
    else
      sudo -n zramctl --reset "$zram_device" || true
    fi
  fi

  if [[ "$memory_percent" == 85 && -e /sys/module/zswap/parameters/enabled ]]; then
    if printf '1\n' | sudo -n tee /sys/module/zswap/parameters/enabled >/dev/null; then
      echo 'Enabled zswap for the runner swap device.'
    fi
  fi

  swap_kib=$(awk '/^SwapTotal:/ { print $2; exit }' /proc/meminfo)
  available_kib=$(df -Pk "$RUNNER_TEMP" | awk 'NR==2 { print $4 }')
  swap_file_kib=$((available_kib - 6 * 1024 * 1024))
  if (( swap_file_kib > 12 * 1024 * 1024 )); then
    swap_file_kib=$((12 * 1024 * 1024))
  fi
  if (( swap_kib < 12 * 1024 * 1024 && swap_file_kib >= 4 * 1024 * 1024 )); then
    swap_file="$RUNNER_TEMP/erdos535.swap"
    if sudo -n install -m 600 /dev/null "$swap_file" &&
        sudo -n fallocate -l "$((swap_file_kib * 1024))" "$swap_file" &&
        sudo -n mkswap "$swap_file" && sudo -n swapon "$swap_file"; then
      echo 'Enabled additional swap on the runner disk.'
    else
      sudo -n rm -f -- "$swap_file"
    fi
  fi
  free -h
  swapon --show || true

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

memory_max=$((mem_kib * 1024 * memory_percent / 100))
memory_high=$((memory_max * high_percent / 100))
echo "Reserving $((mem_kib / 1024 - memory_max / 1024 / 1024)) MiB outside the Lean build."
sudo -n systemd-run --wait --pipe --collect \
  --uid="$(id -u)" --gid="$(id -g)" --working-directory="$PWD" \
  --property="MemoryHigh=$memory_high" --property="MemoryMax=$memory_max" \
  --property=OOMPolicy=kill --property=Nice=10 \
  --setenv="HOME=$HOME" --setenv="PATH=$PATH" --setenv="LEAN_NUM_THREADS=$LEAN_NUM_THREADS" \
  --setenv="RUNNER_TRACKING_ID=${RUNNER_TRACKING_ID:-}" \
  /usr/bin/timeout --kill-after=30s "$minutes" "$HOME/.elan/bin/lake" build "$@"
