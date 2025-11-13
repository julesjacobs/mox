#!/usr/bin/env bash
set -euo pipefail
SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
TARGET="tests/mox"

if [ $# -ge 1 ]; then
  TARGET="$1"
  shift
fi

if [ $# -ge 1 ]; then
  echo "Usage: ./mox.sh [PATH]" >&2
  exit 1
fi

cd "$SCRIPT_DIR"
OCAMLRUNPARAM=${OCAMLRUNPARAM:-v=63}
export OCAMLRUNPARAM
dune exec bin/main.exe -- record "$TARGET"
