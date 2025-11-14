# Mox Playground (WebAssembly)

This folder contains a proof-of-concept WebAssembly build of the Mox typechecker
that runs entirely inside the browser. The OCaml sources are compiled with
`js_of_ocaml` (in wasm mode) and exposed to the front-end as a small API that
accepts a buffer and returns the rewritten text with refreshed `>` result lines.

## What gets built

- `playground/mox_playground.ml` exports `window.MoxPlayground.process`, which
  wraps `Expect.process_lines` so the browser can re-typecheck snippets without
  going through the CLI.
- `playground/app.js` and `playground/index.html` host a Monaco editor with a
  “Process buffer” button that calls into the WebAssembly bundle. The editor
  rewrites the entire buffer with the returned lines (same behaviour as the
  `expect` tests).

## Prerequisites

You need a recent `js_of_ocaml` toolchain with WebAssembly support plus the
`wasm_of_ocaml` compiler:

```bash
opam install js_of_ocaml js_of_ocaml-compiler js_of_ocaml-ppx \
  wasm_of_ocaml-compiler
```

Mac users also need `cmake` and `ninja` available on the PATH (e.g. via
`brew install cmake ninja`) so `wasm_of_ocaml-compiler` can vendor its Binaryen
dependency.

## Building

From the repo root:

```bash
dune build @playground/wasm
```

This compiles the bytecode, bundles it with `js_of_ocaml` for quick local dev
(`mox_playground.bc.js`), **and** uses `wasm_of_ocaml` to emit
`_build/default/playground/mox_playground.bc.wasm.js` plus the associated
`mox_playground.bc.wasm.assets/` directory containing the actual WebAssembly
binary. `index.html` references the `.wasm.js` loader directly out of `_build`,
so no copying is required; just make sure your static server exposes the entire
repo root (including `_build/default`).

## Running the playground locally

1. Build the bundle as shown above.
2. Serve the repository root (so that `/playground` and the files underneath
   `/_build/default/playground/` are reachable). A simple option is:

   ```bash
   python3 -m http.server 8000
   ```

3. Visit `http://localhost:8000/playground/` in a modern browser. The page loads
   Monaco from the CDN, waits for `MoxPlayground` to appear, then enables the
   “Process buffer” button (⌘/Ctrl + Enter is also wired up).

Any exception thrown by the parser/type checker is surfaced in the status banner
instead of crashing the page. When the backend returns successfully, the entire
buffer is replaced with the updated text (mirroring the CLI workflow).
