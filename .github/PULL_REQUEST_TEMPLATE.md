## Contribution

Is this a solve or maintenance? For a solve, name the exact instance and theorem. Follow the [proposal specification](https://github.com/hodge-computer/sextics/blob/main/CONTRIBUTING.md).

## Mathematics

Summarize the method and link `data/<instance-id>/solution.md`. Identify the witness definitions or existence argument, any nonzero quotient, previous mathematical results used, and collaborators.

## Verification

List the checks actually run and their results. If relying on CI for Lean, say so.

For a solve:

- [ ] New solution files are added in one existing `data/<instance-id>/` folder; any companion edits are confined to `formal/lean/HodgeComputer/Constructions/`, `formal/{TECHNIQUES,README}.md`, `docs/*.md`, or `docs/index.json` with no deletions.
- [ ] `proof.json`, `Solution.lean`, and `solution.md` are present; optional solve files are an exact witness and flat Lean helpers.
- [ ] The theorem proves the fixed protected statement without placeholders or unapproved axioms, and any new shared library modules build without warnings.
- [ ] Any JSON witness is bound to the additional protected witness theorem.
- [ ] Protected core Lean files, existing target/context/solve records, verifier, website, and generated files are unchanged.
