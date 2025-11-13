#!/usr/bin/env bash
set -euo pipefail
SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
ENGINE="typeinference"
TARGET="tests/mox"

if [ $# -ge 1 ]; then
  case "$1" in
    check|typechecker)
      ENGINE="typechecker"
      shift
      ;;
    infer|typeinference)
      ENGINE="typeinference"
      shift
      ;;
  esac
fi

if [ $# -ge 1 ]; then
  TARGET="$1"
  shift
fi

if [ $# -ge 1 ]; then
  echo "Usage: ./mox.sh [check|infer] [PATH]" >&2
  exit 1
fi

cd "$SCRIPT_DIR"
OCAMLRUNPARAM=${OCAMLRUNPARAM:-v=63}
export OCAMLRUNPARAM
MOX_DEBUG_LOCK=${MOX_DEBUG_LOCK:-}
export MOX_DEBUG_LOCK
dune exec bin/main.exe -- --engine "$ENGINE" record "$TARGET"
