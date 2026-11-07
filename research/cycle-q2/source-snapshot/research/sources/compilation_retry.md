# Compilation retry — 4 November 2026

## Outcome

**Not compiled.** No Lean executable was available and no toolchain was obtained.
No compiler error about the mathematical source was observed, because source
elaboration did not begin. No mathematical proof is claimed.

## Why the earlier successful records differ

Two kinds of prior success were located in the supplied records:

1. The cycle-q2 compiled research build was a Python rational-system build and
   C++17 solver compilation. Its `BUILD_SUMMARY.json` expressly sets
   `lean_proof_compiled=false`, with `lean` and `lake` absent.
2. The holdout-bundle verification receipt records a real Linux Lean 4.33.0
   environment, the SAME Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`,
   trusted prebuilt dependency caches, 108 source compilations and 45 kernel
   replays. That is an archived receipt, not a new replay here. Its previously
   recorded `/workspace/scratch/.../holdout-research/` environment is not mounted
   in this execution container. Source delivery does not preserve that runtime.

The second record explains how an earlier Lean proof could compile while this
workspace cannot bootstrap. This is not evidence of a contradiction in Lean or
of a source-level failure in the cycle-q2 helper file.

## Diagnosis performed in this run

- PATH probes found curl, git, Python and a C++ compiler; no lean, lake, elan or
  leanchecker was found. A broader filesystem search found no usable Lean runtime.
- DNS probes for elan.lean-lang.org, github.com, raw.githubusercontent.com and
  releases.lean-lang.org failed in this execution container.
- Four direct official HTTPS probes failed with curl exit 6.
- The configured resolver's TCP port and a separate public HTTPS endpoint both
  returned connection-refused errors. These are observations of this runtime,
  not a diagnosis of the user's Mac/network or an assertion about all networks.
- The separate container download action failed as well.
- Read-only GitHub access confirmed the exact v4.33.0 release and its successful
  CI run. Downloading that run's official Linux artifact through the connector
  failed at its documented-in-error size ceiling; no artifact bytes were returned.
- Plugin discovery did not expose a ready Lean execution service. No unrelated
  integration was installed and no remote job was started.

No DNS, firewall, global proxy or security configuration was changed.

## Official artifact retrieval

```text
repo: leanprover/lean4
release: v4.33.0
commit: d8b18978322de05a8f3dba51ef03cf5461676c17
workflow run: 31356129319
artifact: 9051059050 (build-Linux release)
size: 1462041028 bytes
connector ceiling: 536870912 bytes
result: InvalidInputException: Artifact exceeds max size
```

The metadata was visible, but visibility is not an actual installed toolchain.
The release download and artifact attempts did not change the original source.

## Changes actually made

The bootstrap now supports a verified direct release ZIP and explicit existing
compiler/cache paths, without requiring elan. The offline path checks the pinned
version and all nine dependency revisions; missing inputs fail rather than
claiming success. Version checks reject the release candidate and other Lean
versions. Archive extraction rejects escaping paths and symlinks and preserves
executable permissions. The checksum is checked before executing a downloaded
compiler.

The real compiler-check runner now uses the selected prefix instead of assuming
`~/.elan/bin`. No theorem definitions or proofs were modified. The exact upstream
Git blob checks still pass.

## Verification and limitation

The runtime helper has ten passing unit tests, plus a passing offline no-download
failure guard. An initial archive test exposed an error-classification/order
issue, which was fixed; both initial and final logs are retained. Nine prior
Python arithmetic regression tests passed again.

These tests validate only the changed tooling and existing arithmetic code.
No test emulates Lean and presents that as successful proof checking. The
installer and offline exporter have not completed end-to-end with real Lean
binaries in this run.

The remaining operational input is a working same-platform Lean 4.33.0 runtime
with the pinned dependency cache, or working runtime network access to download
those inputs. Once present, `python3 scripts/check_lean.py` performs the actual
build and records its real exit codes. Source-level fixes may still be required;
no claim that the uncompiled helper proofs already typecheck is made.

The remaining mathematical input is still a valid original certificate.
Installing or compiling helper lemmas does not produce it.
