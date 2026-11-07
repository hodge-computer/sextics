# Cycle-q2 research draft and source snapshot

This draft preserves the incomplete Lean development and research history supplied in
[Cycle-q2 Research Attempt](https://chatgpt.com/g/g-p-6a6d301e456881918ba2a163ea5e7e4e-math/c/6aea2396-5700-83ea-85c4-ad3a8a0ba501).
The package was imported on November 6, 2026, for `fqlx` with OpenAI Codex assistance.
The archived reports retain their individual attributions, collaborators, and mathematical sources.

## Reading order

- [Research history](source-snapshot/RESEARCH_HISTORY.md): 70 documented approaches
  and development stages, including failed searches, withdrawn claims, and remaining gaps.
- [Archived strategy atlas](source-snapshot/research/ARCHIVED_STRATEGY_ATLAS.md):
  all 45 nodes of the recovered strategy graph.
- [Source guide](source-snapshot/research/SOURCES.md): included reports and their evidence limits.
- [Lean entry point](source-snapshot/formal/CycleQ2Draft.lean) and
  [normalization account](source-snapshot/NORMALIZATION.md).
- [Saved status](source-snapshot/STATUS.json) and
  [original handoff checks](source-snapshot/HANDOFF_CHECKS.json).

## Proof and compatibility status

The original certificate remains unproved in this snapshot.
`CycleQ2Draft.missing_rational_solution` contains the explicit `sorry` at line 20;
`certificate_draft` depends on it. The missing theorem asks for the actual legal
homogeneous rational solution, including both normalized equations. No complete
certificate, unrestricted nonexistence result, or protected Lean acceptance is claimed.

The archive records its Lean source as **uncompiled**, with no kernel replay.
Historical arithmetic results and saved receipts describe earlier work; they were
not rerun for this import. The source reports distinguish scoped exclusions from
unrestricted nonexistence and preserve corrections to earlier claims.

The separate workspace pins Lean **4.33.0**, Mathlib revision
`db584cd6d46c92f209a44c0f1c829460d327499d`, and its bundled historical verifier.
At import, the maintained repository pins Lean **4.33.1** and uses a different
verifier interface. For example, the archived `HasCertificate F A q` differs from
the maintained `HasCertificate F q A`; the maintained witness also records the
hypersurface and source homogeneity conditions. This draft has not been ported
to that interface or compiled against it. The archived polynomial definitions
of `F`, `A`, and `q = 2` agree with the current
[instance record](../../data/cycle-q2/instance.rec).

The files here are research material outside the maintained Lean library and
the solve-submission directory. There is no `proof.json`, `Solution.lean`, or
`solution.md` submission. The ongoing shared mathematical record is
[Discussion #61](https://github.com/hodge-computer/sextics/discussions/61).

## Source preservation and import checks

All 67 files under `source-snapshot/` are byte-for-byte copies of
`cycle_q2_lean_source_with_research.zip` downloaded from the linked chat.
The ZIP's SHA-256 is
`3e761a1539f69ee1cab361a5c2538edc68c198b75b66d9ba2816bb37fe6c7dbd`.
The original [handoff manifest](source-snapshot/HANDOFF_MANIFEST.sha256) and
[recovery manifest](source-snapshot/RECOVERY_MANIFEST.json) are preserved.

[Import checks](IMPORT_CHECKS.json) record the checks performed for this PR:
archive integrity and source equality, manifest hashes, JSON parsing, local file
references in the handoff documents, ledger/atlas counts, the explicit admission
count, and exact polynomial comparison with the current instance record.
The original chat may require account access; the imported source reports are
available directly in this PR. Links embedded inside historical reports can refer
to unavailable older artifacts and have not all been revalidated.

To check the original handoff hashes from this directory:

```sh
(cd source-snapshot && shasum -a 256 -c HANDOFF_MANIFEST.sha256)
```

Lean compilation, kernel replay, and the historical mathematical checks were
not performed for this archival draft.
