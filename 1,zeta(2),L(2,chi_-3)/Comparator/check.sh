#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."
export LEAN_NUM_THREADS=1

check_toolchain() {
  if ! cmp -s lean-toolchain "$1"; then
    printf 'Toolchain mismatch: %s must match lean-toolchain\n' "$1" >&2
    exit 1
  fi
}

check_toolchain Comparator/lean-toolchain
command -v landrun >/dev/null || {
  printf 'landrun must be installed on PATH\n' >&2
  exit 1
}

expected_version=$(<lean-toolchain)
expected_version=${expected_version##*:v}
check_lean() {
  local version
  version=$(lake env lean --version)
  case "$version" in
    "Lean (version $expected_version,"*) ;;
    *) printf 'Expected Lean %s, got %s\n' "$expected_version" "$version" >&2; exit 1 ;;
  esac
}

check_lean
(cd Comparator && check_lean)
for dependency in \
  .lake/packages/mathlib \
  .lake/packages/lean4export \
  Comparator/.lake/packages/Comparator \
  Comparator/.lake/packages/lean4export \
  Comparator/.lake/packages/lean4checker; do
  check_toolchain "$dependency/lean-toolchain"
done

lean_prefix=$(lake env lean --print-prefix)
landrun --ldd --add-exec --ro / -- "$lean_prefix/bin/lake" --version

lake build
lake build lean4export
(cd Comparator && lake build comparator)
export PATH="$PWD/.lake/packages/lean4export/.lake/build/bin:$PATH"

# Landrun splits its path flags on commas, including commas in the package name.
# A real temporary working directory with links preserves the source and cache.
if [[ $PWD == *,* ]]; then
  source_dir=$PWD
  check_dir=$(mktemp -d /tmp/dirichlet-comparator.XXXXXXXX)
  trap 'rm -rf -- "$check_dir"' EXIT
  shopt -s dotglob
  for entry in "$source_dir"/*; do
    ln -s -- "$entry" "$check_dir/"
  done
  cd "$check_dir"
fi

lake env Comparator/.lake/packages/Comparator/.lake/build/bin/comparator Comparator/config.json
