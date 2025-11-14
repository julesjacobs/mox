# Agent Guide

This project uses `.mox` test files to exercise the parser and type checker. Each test file contains a sequence of source expressions separated by blank lines. After every expression, a line beginning with `>` records the result: either the inferred type (`> unit`, `> (unit + empty)`, etc.) or an error message prefixed with `error:`.

## Running the test suite

1. Execute `dune exec bin/main.exe record tests/mox` from the repository root. The driver walks the `tests/mox` directory, re-typechecks every `.mox` file, and rewrites the `>` lines in place.
2. Inspect the changes with `git status` and `git diff`. Any deltas highlight expressions whose behaviour changed.
3. If new behaviour is intentional, leave the updated `>` lines in place so the suite documents the new expectation. Otherwise, fix the regression and re-run the command until the diff is clean.
4. If you are unable to fix the bug, place a comment before the test indicating that it is a bug. Remove such comments when the bug is resolved.

### Adding tests

- Drop a new `.mox` file inside `tests/mox`. Include only the raw expressions; the `record` command fills in the `>` lines for you.
- Run the workflow above to populate the outputs. Review the diff and stage the test file together with your code change.

Following this loop keeps the test suite authoritative and makes behavioural changes easy to spot in review.

## Updating editor syntax files

If you change `.vscode/mox-syntax/syntaxes/mox.tmLanguage.json`, remember that Cursor/VS Code read the grammar from the packaged `.vsix`, not directly from the workspace file. After editing the grammar:

1. Rebuild the extension from `.vscode/mox-syntax/` with `npx vsce package`, then copy the resulting `.vsix` to `.vscode/mox-syntax.vsix` (Cursor expects that location).
2. Reinstall the package in both editors so they pick up the new scopes:
   - `code --install-extension .vscode/mox-syntax.vsix --force`
   - `cursor --install-extension .vscode/mox-syntax.vsix --force`
   The user wants you to always reinstall after making syntax highlighting changes.
3. Reload the window (“Developer: Reload Window”) to flush the cached syntax data.

Skipping these steps means the editors will continue using the previous grammar even though the repo files changed.
