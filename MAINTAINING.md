# Maintaining the repository

Contributor instructions are in [CONTRIBUTING.md](CONTRIBUTING.md); this document covers the repository, acceptance pipeline, and website maintenance.

## Repository architecture

The project uses direct GitHub PRs with protected Lean verification, GitHub merge permissions, and a trusted publication step. GitHub provides contributor identities, PRs, and discussions; the website backend handles GitHub sign-in and discussion access. Contribution format and checks are documented in [CONTRIBUTING.md](CONTRIBUTING.md); the verification and publication procedure is described below.

Each instance lives permanently in `data/<id>/`. Its protected target and prospective context exist before a solve. A solve PR adds proof sources, an explanation, and optional witness data to that same folder. After a checked merge, the publisher adds an acceptance receipt. The atlas, explanations, PR links, and leaderboard are generated from the accepted sources and receipts. `/data` contains mathematical statements, context, proofs, and acceptance records. It contains no rendering settings or derived coefficient lists. The content builder expands exact expressions into coefficients and writes browser records and rendered explanations to `assets/atlas/`, which is untracked build output. Do not commit this directory.

`formal/lean/` pins the shared contract, Lean toolchain, and mathlib manifest. `scripts/proposals/` implements source restrictions, sandboxed compilation, kernel replay, theorem/axiom auditing, and publication. `.github/workflows/` invokes trusted base-branch code; candidate workflow and setup files are never executed as part of solve verification.

Treat the shared formal library as the Lean counterpart of the book: retain organized, generally useful machinery with explicit scope and concrete applications; keep failed experiments and instance-specific calculations out of it. Reusable constructions belong under `formal/lean/HodgeComputer/Constructions/` when they support concrete applications. Extract accepted machinery through a maintenance PR, preserving its attribution and the original acceptance-backed instance files. New solve PRs import the maintained library and supply their target-specific proof. Build changed shared modules, replay them with `leanchecker`, and check an application against the protected target before merging library changes. The protected dependency-cache key includes the shared Lean sources as well as the pinned toolchain and manifest.

`docs/index.json` and its Markdown sources define the expandable technical chapters. The content builder produces `docs/*.html` and exports the homepage view from `slices/home.json` to `assets/home-scene.json`. Like `assets/atlas/`, these are untracked build outputs; do not commit them. `assets/` contains local runtime scripts, styles, fonts, and meshes. Navigation is parsed by `assets/routes.js`; `leaderboard-view.js` owns ranking requests and rendering, and `discussion-drafts.js` owns drafts across panel mounts. The app and renderer consume `formalStatus` for accepted proof status, independently of available divisor data. `slices/` is the authoritative source for per-instance planes, cameras, and mesh selections; `slices/divisors/` holds display-divisor formulas. `assets/atlas-presentation.json` holds category labels, curated formula typesetting, and its definitions. The atlas and mathematical content are static; sign-in and discussions use the backend API.

Changes on `main` trigger `.github/workflows/deploy-website.yml`, which publishes the static website. Backend deployments are documented in `infra/aws/README.md`.

## Catalogue curation

The catalogue lists fixed instances of the existence problem in `formal/README.md`. `data/catalogue.json` determines displayed instance numbers; append new instances to preserve existing numbers. Solving an instance does not renumber other entries. The sidebar shows both open and solved targets by descending number. Previous/next navigation follows that same order. These numbers are presentation labels; proofs, discussion mappings, and acceptance records use stable instance IDs. Each instance has an exact statement, motivation, mathematical context, and saved visualization.

A target is open until a checked and merged PR has a validated acceptance receipt. The publisher derives solved status, contributor attribution, and leaderboard credit from that receipt. Solution files are first introduced by their solve PR and remain beside the target after acceptance.

Instance descriptions in `why.md` explain the mathematical role of the target against the established state of knowledge. For an open instance, use the cumulative results of the known and solved instances as they stand now. For a solved instance, use the state immediately before its own solution: do not explain it through its own proof or later advances. Exclude discussion progress, proposed constructions, reported searches, and discussion links from both kinds of description. An established result may be explained directly or cited through the book or an applicable earlier accepted construction; removing a discussion link alone does not turn a research report into established context. Keep ongoing investigations in the discussions. The accepted `solution.md` explains the argument and retains its mathematical sources and attribution. `provenance.json` links to the exact statement, mathematical context, discussion, and other atlas targets on the same sextic. Do not treat a restricted negative search as proof of nonexistence.

Before adding a frontier target, screen it against the scope of every established construction, including coordinate changes, source linearity, all-polynomial-source results, finite-cover characters, and proven parameter or pole-order extensions. Breaking one displayed formula or one modular seed is not evidence of escaping the underlying method. Record the precise missing hypothesis and distinguish a known-existence certificate-extraction problem from a new geometric or character boundary. Nearby coefficient variants should not be added merely because their incidence matrices have not yet been calculated. A useful new entry isolates a mathematical obstacle that remains after these checks; an established method may still reveal an unexpected solution later.

A point in the leaderboard records an accepted target, not a claim of a new technique or literature priority. Do not change acceptance criteria retroactively. Progress toward the general even-sextic problem requires extending a method over a sufficiently large parameter family, not simply increasing the number of isolated targets.

Adding or changing targets requires a separate owner-reviewed maintenance PR. Keep the variable order `X0, X1, X2, Y0, Y1, Y2`; check exact rational coefficients, sextic homogeneity, target degree `6q`, and parity under the sign involution. Maintain precise family scope and avoid claiming that a representative example proves a whole family. The catalogue is representative; solving its current entries need not settle the general conjecture.

Meshes are approximations for navigation and exploration. A real slice and camera do not provide evidence of smoothness, topology, or certificate validity. Preserve exact statements independently of rendering settings. A new catalogue entry needs a saved slice in `slices/<id>.json` and typesetting in `assets/atlas-presentation.json`.

## Leaderboard

The board is generated from validated acceptance receipts. Each distinct accepted instance gives one point to its direct PR author. Equal scores are ordered by when the contributors reached that score: compare the acceptance time (solve PR merge time) of each contributor's latest counted solve, earliest first. Alphabetical login order breaks an exact timestamp tie. Displayed ranks follow that order. Do not edit scores manually or award credit merely for local compilation, an unmerged proof, or a status flag.

The atlas index contains each accepted instance’s contributor and acceptance time. The solve board ranks those records directly; profile lookup reads the same published index. Solve scores and attribution have no GitHub API dependency at runtime. Names and avatars come from GitHub profiles through the existing backend; no contributor receives a local profile override or bundled photograph.

The comments leaderboard uses `/api/comment-leaderboard` on the discussion service. It counts comments and replies across mapped atlas discussions and breaks ties by the earliest time a contributor reached their current count. The service caches identity/timestamp metadata and bounded contributor previews for two minutes; it fetches comment bodies only when an uncached contributor is selected, through `/api/comment-leaderboard/<login>`. GitHub remains the source of truth. The visible board refreshes at most once a minute, including on returning to the tab, including edits and deletions, without a commit or website deployment. Deleted accounts and minimized posts are omitted. Never commit discussion snapshots or generate static comment archives for this feature.

Solver portraits link to the contributor's leaderboard entry; the construction header links to the actual merged PR from its receipt. The explanation records collaborators and prior mathematical sources. Documentation contributions retain their authorship but do not add solve points.

## Verification, sign-off, and publication

Solve contributions are direct GitHub PRs. The protected checker validates the exact target and proof, and the owner decides whether to merge it. A separate trusted publisher records acceptance and rebuilds the atlas and leaderboard. No workflow merges a PR automatically.

### Protected checks

Before preparing Lean, CI builds content from the protected checkout, renders the proposed `solution.md` with the publication renderer, validates local file links against that content plus proposed files, and checks formulas with the bundled KaTeX. This check does not fetch external URLs or execute proposal code. `scripts/content.py` resolves Markdown links relative to the source document; a leading `/` selects the repository root.

`solve-proposal.yml` uses trusted base-branch code. Draft PRs wait until marked ready, or until the owner explicitly dispatches a check. Pinned protected Lean dependencies are cached between runs; each submitted proof is still compiled and checked independently. It fetches the PR as data and freezes the base and head commit IDs. A solve may add only permitted proof, witness, and explanation files to one existing `data/<id>/` folder. Existing target, context, infrastructure, and generated files are protected. A mixed solve/maintenance change fails validation; split it into separate PRs.

The checker generates `HodgeTarget` from the base record, and optional `HodgeWitness` from exact witness data. It compiles the proposal inside an OS sandbox, replays every submitted and protected module with `leanchecker` in a separate read-only process, and audits the protected theorem type and transitive axioms. Sequential replay bounds memory use even when a submission has many helpers; unused helpers are checked too. A submitted JSON witness requires an additional theorem binding the exact displayed polynomials to the same protected target. Printed claims are never verification evidence.

Candidate code receives no networking, credentials, or repository write access. Protected target artifacts, candidate artifacts, and the final trusted wrapper have separate write permissions. Linux uses Docker; local macOS checking uses `sandbox-exec`. The pinned toolchain, dependencies, verifier, and OS remain trusted components. Verification fails if isolation is unavailable.

The successful report records exact target/source hashes, base/head commits, the PR author, theorem, witness binding, toolchain, kernel replay, and axiom audit. The workflow posts `solve/lean` on the submitted commit and rejects a result if either PR commit changed during checking. For solve PRs, a green check means the proof passed. Maintenance PRs build the public release; shared Lean changes recheck affected accepted proofs. CI does not request approval or inspect GitHub reviews.

### Merge permissions

GitHub repository access controls who can push and merge. `benediamond` is the only
human with write access; trusted GitHub Actions workflows can publish generated
results. CI validates the proposed changes independently of merge authorization.
There is no CI approval gate for solve or maintenance PRs and no approval-dispatch
step. The post-merge publisher relies on GitHub merge permissions too.
`.github/solve-policy.json` contains verification limits and publication mode.

If publication of an eligible, already-merged solve failed, rerun **Publish accepted
solve** with its PR number. It reuses the successful Lean check against the original
merge parents and source files. A changed head or base requires fresh verification
before merging. This retry cannot turn a failed or unchecked proof into an acceptance.

Use a **merge commit**, preserving the checked head as its second parent. Merge only against the checked base. Squash/rebase merges and base drift fail publication. When merging through GitHub CLI or an owner script, bind the merge request to the reviewed head SHA. Do not merge another solve until the previous publication commit has landed and the next proof has been checked against current main.

### Trusted publication

`publish-solve.yml` runs on a merged PR or an explicit retry. It checks out trusted main and invokes `scripts/proposals/publish.py`. The publisher requires:

- A merged PR into this repository's main branch. GitHub controls who may merge.
- A successful protected workflow run associated with the exact checked head and base.
- Matching workflow/verifier hashes and a matching preserved verification report.
- A merge commit whose parents are exactly the checked base and head.
- The same target and all proof, witness, and explanation hashes in the merged checkout.
- Contributor attribution matching the PR author.

The PR receives a separate `solve/publication` status linking to this workflow. It reports pending, successful, or failed publication independently of `solve/lean`, so a post-merge failure is visible from the PR. It then writes `data/<id>/acceptance.json` and runs the content builder and validators. The builder derives solution metadata from the receipt and original witness in memory. The workflow commits the acceptance receipt to main. Browser records and rendered instance explanations remain build output. A failed or interrupted publication leaves no accepted solve in published output; rerun the workflow once the cause is resolved. The generated acceptance record is durable even after transient CI artifacts expire.

Existing acceptance receipts and their historical authorization fields are preserved. Publication retries validate verifier sources against the original checked base, so older reports remain valid after the authorization code is removed.

The atlas and leaderboard read generated files and need no GitHub service at runtime. Sign-in and discussions use the backend API. The publisher never awards credit from editable claimed identities, an unmerged proof, or a status flag. After acceptance, edit `solution.md` as ordinary reviewed documentation. The site renders the current explanation; the original submission remains in Git history and its acceptance record. Editorial changes do not require another Lean run or a new acceptance record. Changes to the target, Lean sources, proof manifest, or witness require renewed verification.

### Release validation

The Repository build workflow builds and validates the actual published content
and packages the public artifact. `validate-records.py` checks the exact records,
saved slices, and referenced assets; `check-content.py` renders formulas and checks
local links. The build generates current files directly, without a committed
revision hash or a stale-output gate. These checks do not grant formal acceptance.
For shared Lean changes, `scripts/check-library.py --base <commit>` builds and
replays changed modules and their dependents, then rechecks affected accepted
applications against their protected targets.

## Visualization maintenance

`assets/surface.js` provides the page-side `HodgeRenderer` controller. `assets/surface-worker.js` runs `assets/renderer.js` in an OffscreenCanvas worker. `assets/mesh.js` handles manifest fetching, decoding, validation, and cancellation. Superseded loads are aborted. Stationary free-camera and reduced-motion views stop drawing after settling, while GPU fences and the worker watchdog remain active. The page watchdog pauses an unresponsive view after about five seconds so the atlas remains usable. A temporary background context loss permits one fresh worker and canvas on returning to the page. GPU objects from a lost context are discarded. Browsers without the required worker/canvas support retain the atlas without the 3D view.

The page-side interface is:

```js
const view = HodgeRenderer.create(canvas, {
  onStatus({state, message, meta}) {},
  onModeChange(mode) {}
});
await view.setCase(record);
view.setMode('free');
view.setMode('parallax'); // ease back to the saved pose
view.resetCamera();
view.destroy();
```

Creation is synchronous and does not select a case. `setCase` requests a load; use `onStatus` to observe when the surface is ready. The parent UI manages the challenge content, exploration toggle, status pill, and visualization guide. Free-camera controls are trackball rotation, right/shift-drag panning, wheel/pinch zoom, R or double-click to reset, and Escape to return.

Saved `render.mesh` manifests refer to compressed position/normal and index buffers under `assets/meshes/`. Each record's `render.camera` stores a unit quaternion `orientation`, `distance`, and `center`; there are no saved Euler angles. Reset and exploration use this same pose. Mouse and phone parallax apply small rotations and translations along the saved camera's own horizontal and vertical axes, so a rolled view responds in screen directions too. These fields are copied into browser records from `slices/<id>.json` during the build; see [slice curation](slices/curation.md). The homepage uses its separately saved Contact cone view in `slices/home.json`, exported by the content builder to `assets/home-scene.json`. Atlas views retain the box at ±10 and transparent edge fade. The three front-page groups use a precomputed whole compact slice without that cutoff. X-ray reach remains 2.0. X-ray rendering uses up to six depth-peeling layers with a 16-bit floating-point accumulation target. Unsupported graphics or failed allocation pauses the view; the renderer does not switch precision or replace x-ray with opaque rendering.

Mesh manifests explicitly select `float32-p3-n3-phase2-d1` (atlas meshes) or `quantized-p3-n3-phase2-delta-v1` (the compact homepage mesh); both use gzip files and the same geometry validation. The front-page mesh uses quantized position, normal, and complex-observable buffers (about 1.37 MB compressed, 147,298 triangles). The mesh is coarsened with connectivity checks, refined where edges depart from the implicit surface, and reordered for GPU locality. Byte-plane packing of modular differences reduces transfer size without changing the decoded values. A depth prepass limits expensive shading to visible fragments. Parallax uses one camera-smoothing stage and a 60-fps ceiling, subject to GPU readiness. Its divisor shading projects interpolated positions back toward the exact contact-cone sextic using three bounded Newton steps on the unit sphere, avoiding false contours from flat triangle interpolation. The complex color observable is evaluated at that same corrected point, preserving the palette while avoiding triangular phase artifacts near zeros of the vertex approximation. Mobile tilt supplies parallax only when complete orientation readings and sensor access are already available; it never requests permission. Readings are relative to the initial phone pose and adjusted for screen rotation. Returning to the page or changing modes recalibrates the neutral pose.

The numerical surface is obtained from `z = diag(1 or i) B u`, where the columns of the real 6×4 matrix `B` are orthonormal and `u` lies on the unit three-sphere. The phase choices must make the sextic restrict to a scalar-real polynomial. The renderer shows the stereographic projection of the antipodal sphere cover of the projective real slice. Its mesh cannot establish smoothness, topology, or certificate validity. Accepted denominator data controls divisor highlighting independently of the saved geometric mesh.

Meshes are generated offline. The repository ships the saved planes, cameras, and rendered mesh assets. When replacing a mesh, update its saved slice, then delete manifests and buffers no longer selected by any instance or the homepage. Git history retains earlier versions; do not keep unused meshes in the checkout. Equal-polynomial instances should share a slice unless an intentional presentation difference is documented.

Check finite values, normals, index bounds, projected extent, edge lengths, and polynomial residuals. Reject non-real phase restrictions rather than silently taking a real part. Compare refinements around narrow joins: a finite grid can miss small features. Use exact or direct polynomial evaluation to cross-check compact denominator evaluators.

A solve can prove the existential contract without the optional `witness.json` export. Such a proof still earns credit; its denominator must be extracted separately before it can be highlighted. A maintenance change may add `slices/divisors/<id>.json`, citing the relevant definitions and supplying an exact polynomial program. This presentation file does not modify the accepted proof, receipt, witness, or credit. It must not describe an arbitrary geometric curve as the certificate divisor.

Quadric contact · broken reflections uses the exact rational norm exported by
`scripts/export-quadric-contact-divisor.py`; its construction is explained in
`slices/divisors/quadric-contact-broken.md`. It replaces the former numerical
line factors. Its `sliceRestriction` records the saved plane and coordinate
phases: the content builder rejects reuse on a different section. The exact
formula describes the ideal rational-ratio section; the saved plane and mesh
are its floating-point realization. Rendering uses the same polynomial compiler
and divisor shader as every other atlas entry.

The pole-two holdout uses the exact norm exported by
`scripts/export-holdout-q2-divisor.py`, with its derivation in
`slices/divisors/holdout-q2.md`. Its coefficients are rational numbers and
`sqrt(-3)`, evaluated by the shared complex polynomial compiler. Both exact-norm
exporters use `scripts/norm_divisor.py` for characteristic-polynomial interpolation
and compact expressions. The twelve central holdout targets share the section
`Y0/X0 = 23i/20`, `Y1/X1 = 3i/4` and one camera. Only the pole-two target has a
recovered display denominator; it is not a denominator for the other targets.
The saved plane is a floating-point realization of those exact ratios, and
`sliceRestriction` prevents applying the formula to a different saved section.
The obsolete numerical line-factor export has been removed.

All displayed denominators use per-pixel evaluation. Literal polynomials are compiled into multivariate Horner expressions; compact programs retain their arithmetic structure. The fragment shader evaluates each factor and its six ambient derivatives after the inverse stereographic map. Homogeneous coordinate rescaling, including a common scale for quadratic inputs of higher-degree expressions, reduces underflow; dividing by the gradient norm and using pixel derivatives gives curves a consistent antialiased width. Products and powers are displayed as the union of their factors' zero sets, without multiplicity. There is no vertex-sampling fallback. Generated expressions have a 4,096-node budget and run inside the existing visualization worker; context-loss handling and graphics timeouts remain active. Large formulas may still cost more on slower hardware.

Numerical rendering does not replace the surface mesh with an exact surface. A divisor need not intersect a chosen real slice; absence of a bright curve does not imply missing certificate data.

When a literal denominator becomes an exact power on a special slice, a display program may declare `sliceIdentity: {"power": n}`. The content builder checks the polynomial identity `D(Bu) = g(Bu)^n` exactly, with the saved coordinate phases, before displaying `g = 0`. It rejects an incorrect identity or a denominator that vanishes on the entire slice. This removes interpolation artifacts from repeated factors without changing the divisor's support or the accepted witness. Hesse · radial quartic uses `X2 = X0`, where `D = (X0^2 + Y2^2/3)^2`; its displayed square root is only valid on this section.

Atlas divisor evaluation first corrects each interpolated point toward `F = 0` with four bounded Newton steps on the unit sphere, using the same polynomial compiler for every sextic. This prevents a flat mesh triangle's departure from the surface from introducing false divisor contours. Atlas colours retain the shared quadratic stereographic observable. The homepage alone retains its separately curated Contact cone correction and cubic colour observable. These numerical corrections do not establish the existence or topology of a divisor curve.

For an offline adaptive candidate, `node scripts/simplify-surface.cjs INPUT_MANIFEST OUTPUT_MANIFEST [TOLERANCE]` reduces an existing interleaved mesh using endpoint edge collapses. It retains sampled vertex attributes and boundary positions, checks local link and face-orientation conditions, and bounds each collapse against incident planes. This requires Node.js and a C++17 compiler. Use a temporary output folder while comparing against the selected source mesh: the local tolerance is not a global error bound, and sharp color or divisor features require visual inspection. The optional tolerance is an incident-plane distance in display coordinates (default 0.00018). Reduce it for sensitive divisor overlays. The command writes a candidate mesh only; it does not change atlas selections.

`python3 scripts/refine-surface.py INPUT_MANIFEST RECORD_JSON OUTPUT_MANIFEST`
adds samples near curved edges after simplification. Pass the built
`assets/atlas/<id>/record.json`. It uses the record's exact
polynomial coefficients, bounded Newton projection, and conforming edge splits;
splits that reverse a face are rejected. It requires NumPy and supports the
quadratic stereographic color observable, checking that observable against the
source before changing geometry. M₃ uses this additional refinement at its
narrow joins. As with simplification, compare the candidate visually before
selecting it. Neither operation changes the stored slice or camera.
