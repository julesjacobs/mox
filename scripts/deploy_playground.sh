#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT=$(cd -- "$(dirname -- "$0")/.." && pwd)
TARGET_REPO=${1:-"$HOME/git/julesjacobs.github.io"}
PLAYGROUND_DEST="$TARGET_REPO/misc/mox/playground"
TEST_DEST="$TARGET_REPO/misc/mox/tests/mox"
ASSET_SRC="$REPO_ROOT/_build/default/playground"

cd "$REPO_ROOT"

echo "[mox] Building wasm bundle…"
dune build @playground/wasm

mkdir -p "$PLAYGROUND_DEST" "$PLAYGROUND_DEST/mox_playground.bc.wasm.assets" "$TEST_DEST"

echo "[mox] Copying playground assets to $PLAYGROUND_DEST"
cp playground/index.html playground/app.js "$PLAYGROUND_DEST/"
if [ -f "$PLAYGROUND_DEST/mox_playground.bc.wasm.js" ]; then
  chmod u+w "$PLAYGROUND_DEST/mox_playground.bc.wasm.js"
fi
cp "$ASSET_SRC/mox_playground.bc.wasm.js" "$PLAYGROUND_DEST/"
rsync -a --delete "$ASSET_SRC/mox_playground.bc.wasm.assets/" "$PLAYGROUND_DEST/mox_playground.bc.wasm.assets/"
cp tests/mox/editor.mox "$TEST_DEST/"

cd "$TARGET_REPO"
echo "[mox] Committing and pushing to $(pwd)"
git add misc/mox/playground misc/mox/tests/mox/editor.mox
git commit -m "Update Mox playground" || true
git push
