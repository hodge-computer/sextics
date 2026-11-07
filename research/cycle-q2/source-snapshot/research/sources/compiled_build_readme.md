# Cycle-q2 — compiled research build

**Build status:** the supplied rational-current compiler and C++ solver were
built and replayed on 4 November 2026. **Certificate status: missing.**
This package does not contain a completed `(D,N0,...,N5,Q)` tuple or a Lean
existence proof. A successful software build is not the polynomial identity.

## What was actually rebuilt

- `model/affine_current_circuit.json`: 91,269-node parent affine system.
- `model/nine_class_current_system.json.gz`: 98,645-node trace-zero system.
- `model/proper_boundary_2_2_5_system.json.gz`: 119,215-node rational system
  with proper/infinity/finite-branch block sizes 2+2+5. All three variables
  P,U,Z and the compiled moving-frame derivative terms are retained.
- `solver/solve_mod_checkpoint`: compiled C++17 checkpointed finite-field
  elimination executable. The included binary is Linux x86-64; rebuild it
  from the provided C++ source on other platforms.

Both compressed model outputs match the archived SHA-256 values byte-for-byte.
The 119,215-node model hash is
`6f91f942aff1f8e136d878dc6f1f8b3c395d6dd1569b75a1aa0729611b34def1`.

These are the build targets actually present in the two supplied archives.
They are not the separate 1,905,243-node rank-six full-source circuit described
in other reports. That newer source circuit was not rebuilt in this run.

## Rebuild

Use Python 3 and a C++17 compiler (`g++` or `clang++`). The model compiler and
modular replay use the Python standard library. The small exact symbolic test
also needs SymPy 1.14.0.

```sh
python -m pip install -r requirements.txt
python build.py
```

No package installation or network request is performed by `build.py` itself.
A zero exit status means the documented research build and replays passed.
It **does not** mean an original certificate was obtained. The output always
separates the build verdict from `certificate_gate` in `BUILD_SUMMARY.json`.

## Checks executed and their scope

Before modifying a working copy, the original archive manifests were checked:
1,095 continuation records and 1,925 checkpoint records. Duplicate dependencies
were restored as required. Their source hashes and the fresh execution logs are
in `provenance/` and `logs/`.

The model replays verify physical character weights for all nodes, then use
four exact finite-field first-derivative probes to test gauge identities,
source transforms, residue blocks, and related checks. Those probes are
implementation checks, not generic proofs of a rational primitive. The separate
symbolic logarithmic-form verifier checks four characteristic-zero identities.

The C++ solver's calibration tests use known positive and negative finite-field
systems. Returned witnesses and interrupted checkpoint recovery are checked.
No new full cycle-q2 linear-system solve was executed in this build.

The compiled model contains `full_certificate: false`. The missing work is a
rational current closing its complete source, followed by transport to the
original coordinates and the full original polynomial identity. Its coupled
proper/boundary equations are preserved in
`model/PROPER_AND_BOUNDARY_BLOCKS.md`.

## Exact original acceptance target

See `TARGET.json` for the unchanged F, A, q=2, variable order, and requirements.
The required identity is

```text
A*D^2 - 2*D*sum(N_i*partial_i(F))
 + F*(D*sum(partial_i(N_i)) - sum(N_i*partial_i(D))) = F^3*Q.
```

D must be nonzero homogeneous and coprime to F over C. Each N_i must be
homogeneous of degree deg(D)+7. Q is an unrestricted polynomial. No original
candidate is present, so this identity was not run on a completed tuple.

Neither original archive contains a `.lean` source file. The current runtime
has no Lean/lake executable. No kernel-checked existence theorem is claimed.

## Provenance

The mathematical source files in `model/` and `solver/` are unchanged copies
from the two recovered user Library archives. `build.py`, this README, the
machine-readable build status, and packaging metadata are new build tooling.
No mathematical source closure or new research theorem is claimed. Original
README statements are retained under `provenance/`.

The final zip intentionally contains the minimal runnable build, not the full
94 MB collection of historical searches. The original inputs are identified
by size and SHA-256 in `provenance/SOURCE_ARCHIVES.json`. Logs distinguish the
archived receipts from checks freshly executed during this build.
