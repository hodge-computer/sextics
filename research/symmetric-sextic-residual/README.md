# Symmetric sextic: partial Lean development and contact witnesses

This draft preserves the latest research packet from
[Ben Diamond Meaning](https://chatgpt.com/g/g-p-6a6d301e456881918ba2a163ea5e7e4e-math/c/6aee2915-b568-83ea-8d39-cd15c7be4120),
imported on November 6, 2026, for `fqlx` with OpenAI Codex assistance.
The packet's latest reports are dated November 7 UTC. Original mathematical
attributions, collaborator credits, historical receipts, and corrections are retained.
The shared instance discussion is
[Discussion #117](https://github.com/hodge-computer/sextics/discussions/117).

**The packet does not prove the protected `HasCertificate F 1 A` theorem.**
It defines the actual relative rational primitive that is needed and proves
conditional affine clearing from such a primitive. It does not prove that the
primitive exists, and the final affine-to-homogeneous assembly is also unfinished.
The repository's [mathematical context](../../data/symmetric-sextic-residual/why.md)
already supplies a geometric existence argument; this archive records partial
formalization, rather than formal acceptance of that argument.

## Reading order

- [Latest status and reproduction notes](source-snapshot/README.txt).
- [Primitive endpoint](source-snapshot/SymmetricPrimitiveEndpoint.lean):
  `RelativePrimitive`, its exact differential equation, and
  `clear_relative_primitive`.
- [Transport audit](source-snapshot/weighted_primitive_transport_audit.txt) and
  [scope audit](source-snapshot/independent_scope_audit.txt).
- [Contact-span status](source-snapshot/CONTACT_SPAN_STATUS.txt) and
  [finite-witness interpretation](source-snapshot/research_span/contact/CONTACT_SPAN_INTERPRETATION.txt).
- [Geometric formalization gaps](source-snapshot/research_primitive/geometry/GF_feasibility.txt)
  and [direct-route analysis](source-snapshot/research_primitive/direct/CONTACT_DE_RHAM_CONSTRUCTION.txt).
- [Earlier development](source-snapshot/PREVIOUS_DEVELOPMENT.txt),
  [contact work](source-snapshot/PREVIOUS_CONTACT.txt),
  [trace work](source-snapshot/PREVIOUS_TRACE_COMPUTATION.txt), and
  [solver findings](source-snapshot/research_blocker/trace_blocker_findings.txt).

## Exact target and remaining obligations

The archived [input](source-snapshot/inputs/instance.rec) is byte-identical to the
current [protected record](../../data/symmetric-sextic-residual/instance.rec).
In the chart `X = (1+v, 1-v, b)`,
`Y = (c+lambda*v, c-lambda*v, d)`, write `H = f(lambda,b,c,d,v^2)` and
`P = b*d*(1-u)*(c^2-lambda^2*u)`. The required primitive consists of three
rational functions in the actual chart function field satisfying

```text
E_b(beta_0) + E_c(beta_1) + E_d(beta_2)
  = 2*(f_u*P_u - f_uu*P)/f_u^3, evaluated at u=v^2.
```

The six latest modules bind the equation and source to the protected sextic,
establish the chart's irreducibility and nonzero normal derivative, construct
the tangent derivations, verify the full chart Jacobian, and derive legal
affine polynomial identities from an inhabitant of `RelativePrimitive`.
Their conclusion includes a nonzero denominator relatively prime to `H` and
a cleared defect divisible by `H^2`.

The unresolved steps are:

1. Identify the actual contact correspondence and finite functional with the
   required de Rham/cohomology map, and formalize the finite arithmetic witnesses.
2. Prove the support-to-function-field exactness implication, supplying
   `Nonempty SymmetricPrimitiveEndpoint.RelativePrimitive`.
3. Assemble the affine transport and homogeneous clearing into the protected
   certificate, through the earlier `SymmetricRegularCurrent` endpoint.

The finite rank computation alone does not provide a rational primitive.
The archived direct-route countermodel explains why arbitrary trace weights
cannot replace the required closed weights. Historical failed searches retain
their stated bounds and do not establish unrestricted nonexistence.

## Verification performed for this import

[Import checks](IMPORT_CHECKS.json) record ZIP integrity, all 1,838 original
package-manifest hashes, byte equality of the 742 included files, parsing of
277 archived JSON files, and exact input equality. All 69 modules listed in
the original module manifest are present; there are 75 Lean files including
audit inputs. A comment-stripped token scan found no `sorry`, `admit`,
`native_decide`, or custom `axiom` tokens. This scan is not a kernel audit.

Four Python checks were rerun, with fresh receipts kept separately from the
archived evidence:

- [Contact rank](verification/contact_jet_rational_replay.json): exact rational
  reconstruction certifies rank 48, with total inverse defect bounded by `2^(-981)`.
- [Contact smoothness minor](verification/contact_curve_smoothness_rational_replay.json):
  the 84-by-84 minor has a ball defect bound of `2^(-94)`, with the checker's
  stated complete-intersection scope.
- [Source and Jacobian audit](verification/weighted_primitive_transport_source_audit.json):
  all five exact symbolic identities pass, including `det(J) = 4*a^5*v`.
- [Trace-weight countermodel](verification/trace_closedness_counterexample_receipt.json):
  the finite trace/jet rank shortcut fails without the closedness hypothesis;
  this is not an obstruction for the symmetric-sextic target.

These checks do not prove the geometric identification, primitive existence,
or final certificate. **No Lean compilation, kernel replay, or fresh transitive
axiom audit was performed for this import.** The original receipts report
compilation and replay of the six latest modules and an audit of 51 public
theorems; those remain archived evidence, not new validation.

The repository content build and both validators passed: 82 records, 10 chapters,
6,923 rendered formulas, and links/routes in 160 HTML files. All 22 local file
links in this guide resolve. Whitespace checks pass for the new guide, metadata,
and replay receipts; historical whitespace findings in the source snapshot are
preserved to keep the imported bytes unchanged.

The archived environment pins Lean 4.33.1, mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, and Sextics commit
`ca173aad142bd5f6bf5dd156b6798223a45df54f`. At import base
`2d60d08d25fba3e02162b39d4c50f6b467e7f506`, the complete `formal/lean/`
tree is unchanged from that pinned commit. The historical Lean replay script
nevertheless requires its exact pinned checkout. Rebuilding from this source
archive requires preparing the upstream Lean dependencies and compiling the
listed modules in order; compiled objects are not included here.

For the four Python replays, use Python 3.11 with `sympy==1.14.0` and
`python-flint==0.9.0`. Work in a scratch copy because the historical scripts
write receipts beside their source:

```sh
replay_dir=$(mktemp -d)
cp -R research/symmetric-sextic-residual/source-snapshot "$replay_dir/packet"
cd "$replay_dir/packet"
python3 weighted_primitive_transport_source_audit.py
python3 research_primitive/direct/trace_closedness_counterexample.py
python3 research_span/contact/check_contact_jet_witness.py
python3 research_span/contact/check_contact_curve_smoothness.py
```

## Preservation and omissions

The downloaded `symmetric_sextic_contact_repair_20261106.zip` has SHA-256
`51ff792e036f2831fbee654a1699332448d91c9e40b493edd99fce83ada7e933`.
[IMPORT_MANIFEST.json](IMPORT_MANIFEST.json) records the size and hash of every
one of its 1,839 files, marking 742 included files and 1,097 omissions.
Included files are byte-for-byte copies. They preserve all listed Lean source,
research reports, exact replay inputs, historical logs, and original manifests.

Omissions comprise the vendored solver trees/builds, compiled Lean objects,
Python bytecode, native checkpoint/cache files, nested source archives,
regenerable solver `.ms` inputs, and the superseded 800-digit discovery
approximation. The exact 48-jet witness and independent rational checker are
included. Original package manifests still name omitted files; they describe
the downloaded ZIP, not a complete manifest of this selected snapshot.

The separate six-part, approximately 1.48 GB checkpoint archive was not
downloaded or verified. Its original hashes and account-dependent restoration
links are retained in [CHECKPOINT_DOWNLOADS.txt](source-snapshot/CHECKPOINT_DOWNLOADS.txt).
Other historical links and restoration procedures have not all been tested.
Third-party foundation audit metadata is preserved, but the nested external
source archive is omitted and no external Lean foundations were imported.

This research directory is outside the maintained Lean library and the solve
submission path. It adds no `proof.json` or accepted solution and changes no
existing instance, verifier, library module, website source, or generated data.
