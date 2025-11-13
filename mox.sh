#!/usr/bin/env bash
set -euo pipefail
SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
ENGINE=${1:-typechecker}
case "$ENGINE" in
  check|typechecker) ENGINE="typechecker" ;;
  infer|typeinference) ENGINE="typeinference" ;;
  *)
    echo "Usage: ./mox.sh [check|infer]" >&2
    exit 1
    ;;
 esac
cd "$SCRIPT_DIR"
dune exec bin/main.exe -- --engine "$ENGINE" record tests/mox
