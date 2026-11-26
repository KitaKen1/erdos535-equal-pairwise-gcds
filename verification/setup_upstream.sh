#!/usr/bin/env bash
set -euo pipefail

mkdir -p "$GITHUB_WORKSPACE/verification/results"
git init "$RUNNER_TEMP/openai-math"
git -C "$RUNNER_TEMP/openai-math" remote add origin https://github.com/openai/math.git
git -C "$RUNNER_TEMP/openai-math" fetch --depth=1 --filter=blob:none origin "$OPENAI_MATH_COMMIT"
git -C "$RUNNER_TEMP/openai-math" sparse-checkout set lean
git -C "$RUNNER_TEMP/openai-math" checkout --detach "$OPENAI_MATH_COMMIT"
cd "$RUNNER_TEMP/openai-math/lean"
lake update
if [[ "${1:-}" != --plan ]]; then
  lake exe cache get Mathlib
fi
