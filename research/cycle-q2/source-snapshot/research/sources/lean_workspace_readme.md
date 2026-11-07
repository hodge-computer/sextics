# Cycle-q2 — Lean-ready workspace and fixed-denominator tools

**Status on delivery: LEAN SOURCE PREPARED; INSTALLATION BLOCKED IN THIS SANDBOX.**

The attempted installer failed because the sandbox could not resolve
`elan.lean-lang.org`. A separate GitHub download also failed. No Lean/Lake
executable was present. Consequently **no Lean compilation, kernel replay, or
original existence proof is claimed**. The Python arithmetic tests and the C++
denominator regression checks were actually executed.

This workspace is local to the delivered files. It has not installed anything
on the user's Mac, changed a connected repository, or changed the scheduled
jobs' execution environment. Those jobs do not acquire a persistent Lean
installation merely because this zip exists.

## 1. Install and check on a network-enabled Linux or macOS machine

Prerequisites: `git`, `curl`, and `python3`. On macOS, install Xcode Command Line
Tools if `git` is not available. Open a terminal in this extracted directory.

```sh
bash scripts/setup_lean.sh
python3 scripts/check_lean.py
```

The setup uses the official elan installer, without changing the global default
toolchain or editing shell profiles. It installs the pinned Lean toolchain,
retrieves the locked Mathlib dependencies and cache, and preserves the dependency
lock. It does not run a certificate search or send/publish any repository changes.

**Version pins, read from the project on 4 November 2026:**

- Hodge Computer repository commit: `83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0`.
- Lean: `leanprover/lean4:v4.33.0`.
- Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`.
- All nine dependency revisions are retained in `formal/lake-manifest.json`.

`formal/HodgeComputer/Verify.lean` and `formal/HodgeTestbed/Algebra.lean` are
byte-identical copies of the pinned upstream sources; their Git blob hashes
are checked before setup and compilation. The protected `Verify`/`HasCertificate`
statement is not modified. `provenance/UPSTREAM_LOCK.json` records the pins.

`check_lean.py` runs `lake build CycleQ2Workspace` and then the real Lean compiler
on the source, audits the displayed dependencies of the three helper theorems,
and writes `logs/LEAN_CHECK.json`. Missing tools, errors, version drift, or proof
placeholders do not yield a success status. The helper source is **uncompiled
in this delivery**, so a successful build on the network-enabled machine is
still required. The workspace does not assert `OriginalGoal`.

For editing, open the `formal` folder with the official Lean 4 VS Code extension.
If your terminal does not find elan, put `${ELAN_HOME:-$HOME/.elan}/bin` on PATH.
The extension recommendation is included. No editor is installed by the script.

## 2. What changed in the denominator

The old exported polynomial tuple had a represented common factor `H` of degree
48, stored as atom 7960. It divides its denominator and every nonzero numerator.
Canceling this factor gives **the identical rational vector field**:

```
D_old = H D_reduced;  N_old,i = H N_reduced,i.
deg D: 3726 -> 3678.
deg N_i (nonzero): 3733 -> 3685.
```

The exact product-rule identity is

```
E(H*D, H*N) = H^2 E(D,N).
```

The cancellation is checked as a generic algebraic identity of the stored
polynomial products. The independent C++ checker recomputes the full original
six-variable defect, including all derivatives. It confirms that the reduced
current STILL FAILS: its quadratic defect coefficient is 1005 modulo 1009, and
211 modulo 1013, at the previously saved legal test points.

This is a representation cleanup, **not** a new rational primitive, a minimal
denominator claim, or a proof that all numerators for this denominator fail.
The existing denominator was already legal. Its current's nonzero remainder,
not its degree or software representation, is the missing mathematics.

The old auxiliary remainder and quotient roots remain under the names `old_R`
and `old_Q`; they are not falsely labeled as polynomial roots for the new
clearing denominator. The saved identity is `H^2 E_reduced = -F^2 old_R+F^3 old_Q`.
The generic ambient identity is inherited from the original packet, not newly
proved by the finite-prime checks. The current-equality cancellation is exact.

Files: `denominator/current_reduced.json.gz`, `denominator/CLEANUP.json`, and
`denominator/REJECT_1009.json`, `REJECT_1013.json`.

## 3. Fixed-denominator search

`search/fixed_denominator.py` works over exact rational coefficients with the
immutable original F, A, q=2. It uses Python's standard library. It:

1. Rejects zero, inhomogeneous, or F-divisible denominators.
2. Keeps all six numerator components and unrestricted polynomial Q at the
   forced homogeneous degree; Q is not set to zero unless its degree is negative.
3. Uses the full source-character block when D has one character under the
   actual diagonal symmetry. Mixed-character D disables that filtering.
4. Builds the exact linear coefficient system and supports exact sparse rational
   elimination, subject to explicit memory-safety size limits.
5. Recomputes the literal ORIGINAL polynomial identity on any returned candidate.

A rational solution of the coefficient system is not called a Lean theorem.
The script cannot replace the missing mathematical choice of a useful D.
`search/denominator.json` therefore has `D: null`: **no new unexcluded search
denominator has been chosen**, and the runner refuses to pretend otherwise.
The reduced old circuit is NOT automatically a suitable finite-search profile.
Do not try to densely expand its degree-3678 numerator space.

After selecting and entering an explicit sparse D, first preview:

```sh
python3 search/fixed_denominator.py search/denominator.json --out search/preview.json
```

Then solve only the stated finite space:

```sh
python3 search/fixed_denominator.py search/denominator.json --solve --out search/result.json
```

The default cap is 2500 unknown coefficients and 30000 rows. Use
`--max-columns`/`--max-rows` consciously when changing them. There is no claim
that these caps are sufficient for the original problem. Large circuit inputs
need a circuit-adapted basis and are not accepted as sparse expanded polynomials.

A term is encoded as

```json
{"coefficient": [1, 2], "powers": [3, 1, 0, 1, 1, 0]}
```

in the ordered variables `(X0,X1,X2,Y0,Y1,Y2)`. A polynomial is a list of these
terms. Coefficients and exponents are parsed as data, not executed as code.
For a smaller explicit subspace, supply `supports`: seven lists of exponent
vectors, one per N_i followed by Q. The verdict then concerns only that space.

`search/example_format_only.json` uses D=1 ONLY as a format/preview example,
not a proposed research direction. No new original cycle-q2 solve was run in
this setup task. Existing exclusion results are not silently overridden.

A candidate JSON with keys D, N (six polynomials), Q can be independently checked:

```sh
python3 search/fixed_denominator.py candidate.json --check-candidate --out candidate_check.json
```

This is an exact arithmetic check, not the publisher's accepted export schema
or a replacement for all the formal `Verify` obligations.

## 4. Tests actually executed

To run the arithmetic tests, install the optional test dependency:

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -r requirements.txt
.venv/bin/python search/test_fixed_denominator.py
python3 scripts/check_source_lock.py
bash -n scripts/setup_lean.sh
```

Nine Python tests passed. They include an independent SymPy reconstruction of
the full six-variable defect and all seven column types, positive/negative
linear-system calibrations, invalid-denominator rejection, and rejection of a
forged zero-current certificate. The manufactured-source calibration is marked
as such; it is NOT the actual monomial A and is NOT a certificate attempt.

To reproduce the safe denominator cancellation and its C++ regression checks:

```sh
python3 scripts/cleanup_denominator.py
python3 inputs/cycle_q2_compiled_continuation/export_checker_program.py \
  denominator/current_reduced.json.gz denominator/current_reduced_program.txt
mkdir -p .tooling
g++ -O2 -std=c++17 scripts/check_reduced_current.cpp -o .tooling/check_reduced_current
.tooling/check_reduced_current denominator/current_reduced_program.txt 1009 982 776 604 497 616 182
.tooling/check_reduced_current denominator/current_reduced_program.txt 1013 634 836 152 51 690 652
```

The successful regression is a **confirmed rejection**, not certificate success.
The expected H-squared defect is the old defect, not the new defect unscaled.

## 5. Exact next mathematical obligation

The target remains a legal homogeneous D and six correctly graded N_i with

```
A D^2 - 2D sum_i N_i F_i + F(D div N - N.grad D) = F^3 Q.
```

No such tuple or closed Lean existence theorem is included. Lean provides the
proof-checking environment; it does not automatically select or repair D.
