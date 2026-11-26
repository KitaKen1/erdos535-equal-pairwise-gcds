#!/usr/bin/env bash
set -euo pipefail

usage() {
  printf 'Usage: %s [--reduction | --comparator TOOL_DIR] [path/to/upstream/535.lean]\n' "$0" >&2
  exit 2
}

reduction=false
comparator_dir=
if [[ "${1:-}" == "--reduction" ]]; then
  reduction=true
  shift
elif [[ "${1:-}" == "--comparator" ]]; then
  [[ "$#" -ge 2 ]] || usage
  comparator_dir="$(cd -- "$2" && pwd)"
  shift 2
fi
[[ "$#" -le 1 ]] || usage

verification_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
fc_source="${1:-$verification_dir/reference/535.lean.txt}"
fc_source="$(cd -- "$(dirname -- "$fc_source")" && pwd)/$(basename -- "$fc_source")"
source_dir="$verification_dir/../lean"
build_dir="$(mktemp -d)"
trap 'rm -rf -- "$build_dir"' EXIT
export LEAN_PATH="$build_dir${LEAN_PATH:+:$LEAN_PATH}"

cd -- "$source_dir"
lean --version
mkdir -p -- "$build_dir/Erdos535"
for module in Statement Encoding Strong Counting UpperBound Reduction; do
  lean -DwarningAsError=true -o "$build_dir/Erdos535/$module.olean" "Erdos535/$module.lean"
done
if [[ "$reduction" == true ]]; then
  python3 "$verification_dir/check_against_fc.py" --reduction "$fc_source" "$build_dir/Audit.lean"
else
  lean -DwarningAsError=true -o "$build_dir/Erdos535.olean" Erdos535.lean
  python3 "$verification_dir/check_against_fc.py" "$fc_source" "$build_dir/Audit.lean"
fi
lean -DwarningAsError=true "$build_dir/Audit.lean" | tee "$build_dir/axioms.log"
python3 - "$build_dir/axioms.log" <<'PY'
from pathlib import Path
import re
import sys

output = Path(sys.argv[1]).read_text()
matches = re.findall(r"'(Erdos535\.[^']+)' depends on axioms: \[([^]]*)\]", output)
allowed = {"propext", "Classical.choice", "Quot.sound"}
if len(matches) != 3:
    raise SystemExit("Expected an axiom report for each of the three declarations.")
for name, report in matches:
    axioms = {entry.strip() for entry in report.split(",") if entry.strip()}
    if axioms - allowed:
        raise SystemExit(f"{name} uses unapproved axioms: {', '.join(sorted(axioms - allowed))}")
print("Verified: three definitional type equalities and the standard axiom allowlist.")
PY

if [[ -n "$comparator_dir" ]]; then
  exporter="$comparator_dir/.lake/packages/lean4export/.lake/build/bin/lean4export"
  targets=(
    FCReference.erdos_535
    FCReference.erdos_535.variants.first_open_case
    FCReference.erdos_535.variants.sunflower_strong
    propext Classical.choice Quot.sound Quot Quot.mk Quot.lift Quot.ind
    optParam autoParam semiOutParam outParam
  )
  for pair in challenge:FCChallenge candidate:FCCandidate; do
    mode="${pair%%:*}"
    module="${pair#*:}"
    python3 "$verification_dir/check_against_fc.py" --comparator "$mode" \
      "$fc_source" "$build_dir/$module.lean"
    lean -DwarningAsError=true --root="$build_dir" -o "$build_dir/$module.olean" "$build_dir/$module.lean"
    "$exporter" "$module" -- "${targets[@]}" > "$build_dir/$module.ndjson"
  done
  LEAN_PATH="$comparator_dir/.lake/build/lib/lean:$comparator_dir/.lake/packages/lean4export/.lake/build/lib/lean" \
    lean --run "$verification_dir/Compare.lean" "$build_dir/FCChallenge.ndjson" "$build_dir/FCCandidate.ndjson"
  for module in Statement Encoding Strong Counting UpperBound Reduction; do
    leanchecker --verbose "Erdos535.$module"
  done
  leanchecker --verbose Erdos535
fi
