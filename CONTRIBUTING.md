# Contributing

Contribute a Lean proof for a fixed instance, share mathematical progress in its discussion, or improve the project. AI agents should use [AGENTS.md](AGENTS.md) for their working sequence.

- [Solve an instance](#solve-an-instance): exact PR format, theorem, witness schema, and verification commands.
- [Discuss an instance](#discuss-an-instance): website and GitHub CLI participation.
- [Improve the project](#improve-the-project): documentation and maintenance contributions.

## Solve an instance

Contribute with the intention of returning results to this shared project. Private experimentation and draft preparation are welcome; useful outcomes should enter a PR or discussion no later than their announcement or publication elsewhere. Credit the people who did the work and the prior results they used. Submit only material you are authorized to publish and contribute. Agents should follow the [participation policy](AGENTS.md#return-results-to-the-project).

Contribute through a direct GitHub pull request for one fixed instance. Add the proof and explanation to that instance's **existing** `data/<instance-id>/` folder. The files remain there after acceptance; there is no separate submissions directory. GitHub supplies the contributor identity from the PR author.

### Start here

1. Read the [formal contract](formal/README.md). Agents can use [AGENTS.md](AGENTS.md) for the working sequence.
2. Choose an instance from `data/catalogue.json`. Read its `instance.rec`, `why.md`, and `provenance.json`. Keep its exact `(F,q,A)` fixed; the variable order is `X0, X1, X2, Y0, Y1, Y2`.
3. Start a branch from the latest upstream `main`. Check for an existing `proof.json` and open PRs for that instance. This format accepts the first proof for an instance; revisions to an accepted proof need separate owner review.
4. Add only the solution files listed below. Do not edit or remove existing files.
5. Prove the exact theorem, explain the mathematics, and run the local check. Inspect the complete diff.
6. Push the branch to your fork and open a PR against `hodge-computer/sextics:main`. Follow the [PR title and description requirements](#pr-title-and-description) below.
7. Address verification failures in the same PR. Once `solve/lean` passes, leave the PR ready for the owner to merge. Do not request a separate GitHub approving review; the owner reviews the explanation and their merge is the final sign-off.

### Files

```text
data/<instance-id>/
  instance.rec       # existing: protected exact statement and presentation
  why.md             # existing: protected motivation
  provenance.json    # existing: protected mathematical context
  proof.json         # ADD: manifest below
  Solution.lean      # ADD: theorem matching the protected target
  solution.md        # ADD: mathematical explanation displayed on the website
  witness.json       # optional ADD: exact displayed polynomial witness
  Helper.lean        # optional ADD: flat Lean helper modules
```

The manifest has exactly these fields when no JSON witness is submitted:

```json
{
  "schemaVersion": 2,
  "instanceId": "your-instance-id",
  "theorem": "Submission.certificate"
}
```

With `witness.json`, add exactly one further field: `"witnessTheorem": "Submission.witness"`.

The trusted publisher adds `acceptance.json` and derives `solution.rec`, the rendered content, the atlas status, and leaderboard credit **after** an eligible merge. Do not submit these files or manually edit generated JSON/HTML. Attribution, PR URLs, and acceptance dates come from the reviewed GitHub event, not editable manifest fields. After merging, the PR's separate `solve/publication` check reports whether acceptance and leaderboard updates were recorded, with a link to any failure. Website deployment follows successful publication.

### Protected Lean statement

The verifier generates `HodgeTarget` from the **base branch's** exact target and requires a closed theorem of this type:

```lean
import HodgeTarget

theorem Submission.certificate :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q := by
  -- Supply a complete proof here.
```

This is a statement skeleton, not a proof. The manifest names the actual fully qualified theorem. Do not add parameters, assumptions, placeholders, or replacement definitions of the protected target. Do not submit `HodgeTarget.lean`.

`HodgeComputer.Verify` is the finite witness interface over complex coefficients: a nonzero homogeneous denominator, six numerators of the required degrees, relative primality, and the full cleared divisibility identity. A nonzero quotient is allowed; the problem is not restricted to strict certificates or bounded denominator degrees. A nonconstructive argument may prove the same existential statement without exporting a witness.

#### Optional displayed witness

`witness.json` has exactly these fields:

```json
{
  "d": 4,
  "D": "exact polynomial expression",
  "N": ["N0", "N1", "N2", "N3", "N4", "N5"],
  "Q": "exact polynomial expression"
}
```

The strings above are placeholders. Use actual polynomial expressions in `X0, X1, X2, Y0, Y1, Y2`, integer literals, `+`, `-`, `*`, nonnegative integer powers `**`, and rational coefficients formed by division by a nonzero integer. No floats, function calls, new variables, or polynomial denominators are accepted. `d` is a nonnegative integer and `N` has exactly six entries. Zero components are written `"0"`.

The verifier creates protected definitions in `HodgeWitness`. In addition to the existential theorem, prove:

```lean
import HodgeWitness

theorem Submission.witness :
    HodgeComputer.Verify HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q
      HodgeWitness.d HodgeWitness.D HodgeWitness.N HodgeWitness.Q := by
  -- Supply the proof for these exact exported polynomials.
```

This additional binding prevents a correct existence proof from being paired with an incorrect displayed witness. The checker generates `HodgeWitness.lean`; do not submit it.

#### Helpers and limits

Name flat helper files with `[A-Z][A-Za-z0-9_]*.lean` and import them as `Proposal.Helper`. That namespace is the verifier's temporary compilation layout, not a permanent repository directory. `Target.lean`, `Checked.lean`, and `Audit.lean` are reserved. Imports must be on single lines at the start of the module, with no dependency cycles. Trusted imports may start with `Mathlib.`, `HodgeComputer.`, or `HodgeTestbed.`.

Use the [shared constructions](formal/README.md#reusable-constructions) when they apply. Keep target-specific identities in your instance's `Solution.lean` or permitted helpers; avoid copying a complete accepted proof package to reuse its machinery. Additions or changes to the shared library belong in a separate maintenance PR before the solve PR that imports them. The verifier audits the final theorem's transitive axioms, including those of imported results.

Ordinary declarations and tactic proofs are accepted. Custom executable extensions, `axiom`, `sorry`, `admit`, and unchecked native decision procedures are refused. Shared infrastructure changes need a separate maintenance PR. Do not submit binaries, compiled artifacts, symlinks, executable scripts, Lake configuration, nested directories, or unrelated files.

The complete committed diff must consist solely of newly added permitted solution files in **one existing instance folder**. Edits to `instance.rec`, `why.md`, the leaderboard, the website, the verifier, workflows, or any other existing file fail validation. A PR without a solve is treated as maintenance and checked by Repository build. CI does not require an approving review or workflow sign-off; GitHub repository permissions control merging.

Limits are in `.github/solve-policy.json`: 64 files, 16 MiB of source, a 60-minute proof budget, and 14 GiB memory. The memory budget leaves room for the operating system and runner services on GitHub's free 16 GB Linux runners for public repositories. The allowed axiom set is `propext`, `Classical.choice`, and `Quot.sound`.

### Mathematical explanation

Write `solution.md` so the argument is understandable without reading Lean. Begin with one descriptive `#` title for the construction or argument, then use `##` for sections and `###` for subsections. Describe the main idea, the witness or existence argument, all side conditions, and the correspondence to important Lean definitions and lemmas. For a construction, explain `D`, the six numerators, and the quotient, including nonvanishing, degrees, relative primality, and the cleared identity. Use LaTeX for formulas. Identify where previous human mathematical results enter the proof and credit their authors, along with collaborators and relevant AI assistance.

Links to local files are relative to `data/<instance-id>/solution.md`. For example, write `[Lean proof](Solution.lean)`, `[motivation](why.md)`, or `[helper](Helper.lean#L20)`. The file must exist in the repository or be included in your proposal. The website links motivation back to the instance and source artifacts to their readable GitHub pages. Existing repository-root links such as `data/<instance-id>/witness.json` also remain supported. Use full HTTPS URLs for papers, GitHub discussions, and external reproduction packets; verify those external links yourself. Do not use local-machine paths or links to files you have not supplied.

Use `\(...\)` for inline mathematics and `\[...\]` or `$$...$$` for display mathematics in `solution.md`. The PR's **Validate explanation links and displayed mathematics** check uses the same renderer and KaTeX validation as publication. It runs before Lean and names any missing local link or invalid formula. External websites are not fetched by this check.

The direct PR author receives the solve credit under their own GitHub account. Each distinct accepted instance earns one point. Documentation and other contributions retain their authorship but do not independently earn a solve point.

### PR title and description

Use a title such as `Solve <instance-id>: <method>`. Complete the [PR template](.github/PULL_REQUEST_TEMPLATE.md):

- **Contribution:** identify the exact instance and fully qualified theorem.
- **Mathematics:** summarize the method, link `data/<instance-id>/solution.md`, and identify prior results and collaborators.
- **Verification:** list commands actually run and their results. State explicitly if relying on CI for Lean.
- **Solve checklist:** confirm the allowed-file boundary, required files, exact theorem, optional witness binding, and unchanged protected files.

### Local verification

Check the explanation first (Python content dependencies and Node.js are required; no Lean build is needed):

```sh
python3 -m pip install -r scripts/requirements-content.txt
python3 scripts/proposals/check-explanation.py --instance your-instance-id --output /tmp/hodge-explanation-check
```

Install Python 3.11 with `scripts/requirements-content.txt` and the pinned toolchain in `formal/lean/lean-toolchain`. Keep the committed Lake manifest. Prepare dependencies once:

```sh
python3 -m pip install -r scripts/requirements-content.txt
(cd formal/lean && lake exe cache get && lake build HodgeComputer.Verify)
```

The verifier requires macOS with `sandbox-exec`, or Linux with Docker and a non-root user. From the repository root, replace the instance ID below:

```sh
python3 - <<'PY'
import json, sys, tempfile
from pathlib import Path
import yaml
sys.path.insert(0, "scripts/proposals")
from acceptance import accepted_sources
from check import ROOT, module_order
from sandbox import verify

instance_id = "your-instance-id"
folder = ROOT / "data" / instance_id
files = {name: (folder / name).read_bytes() for name in accepted_sources(folder)}
manifest = json.loads(files["proof.json"])
instance = yaml.safe_load((folder / "instance.rec").read_text())
policy = json.loads((ROOT / ".github/solve-policy.json").read_text())
order, imports = module_order(files)
logs = Path(tempfile.mkdtemp(prefix="hodge-proof-check-"))
print(f"Verification logs: {logs}", flush=True)
print(json.dumps(verify(ROOT, files, instance, manifest, order, imports, policy, logs), indent=2))
PY
```

This checks the proof against the checkout's target and exports logs, without contacting GitHub. GitHub additionally validates the complete Git diff, file modes, manifest schema, source sizes, attribution, and immutable trusted base/head commits. A local result is development feedback; it is not a GitHub acceptance receipt. If you rely on CI rather than running Lean locally, say so in the PR.

#### Codex Cloud

Use the checked-in setup script for a reproducible development environment:

```sh
bash scripts/codex-cloud-setup.sh
```

Run this command from the checkout root when configuring the environment's
**Install script** field. The script locates the checkout from its own path, so
invoking it by an absolute path also works from another working directory.
It supports Linux, the normal Cloud environment, and macOS for a local equivalent.

The image must already provide Python 3.11 with `venv`/`ensurepip`, Node.js,
`curl`, `git`, `tar`, a C compiler (`cc`), and `make`; Linux also needs `zstd`
to unpack the Lean release. Debian/Ubuntu may need `python3.11-venv`. The script creates
a Python virtual environment, installs `scripts/requirements-content.txt`, and
installs the pinned Lean toolchain from `formal/lean/lean-toolchain`. It preserves
the committed Lake manifest, then runs `lake exe cache get` and
`lake build HodgeComputer.Verify` in `formal/lean`. No services are required.

Python tooling and elan are stored under `SEXTICS_CLOUD_HOME`, which defaults to
`$HOME/.cache/sextics-cloud`. The Python virtual environment is
`$SEXTICS_CLOUD_HOME/venv`; `ELAN_HOME` defaults to `$SEXTICS_CLOUD_HOME/elan`.
Mathlib checkouts and compiled artifacts stay in `formal/lean/.lake`. Use
absolute paths for installation overrides and the same values in subsequent shells.

Save the following instructions in the environment's **Start skill** so each
new shell restores the tools. Replace `/path/to/sextics` with the actual checkout
path in that environment:

```sh
export SEXTICS_CLOUD_HOME="${SEXTICS_CLOUD_HOME:-$HOME/.cache/sextics-cloud}"
export ELAN_HOME="${ELAN_HOME:-$SEXTICS_CLOUD_HOME/elan}"
export PATH="$SEXTICS_CLOUD_HOME/venv/bin:$ELAN_HOME/bin:$PATH"
cd /path/to/sextics
export ELAN_TOOLCHAIN="$(cat formal/lean/lean-toolchain)"
```

Allow network access for GitHub clones and releases (`github.com`,
`release-assets.githubusercontent.com`, and `releases.lean-lang.org`), Python
packages (`pypi.org` and `files.pythonhosted.org`), and the mathlib cache
(`lakecache.blob.core.windows.net`). Retain the environment's configured proxy
and CA trust. A successful `lake exe cache get` is the cache readiness check;
testing a hostname alone does not establish access to the required artifacts.

Codex saves the Install script and Start skill separately. Test the setup,
publish the environment after a successful run, and start a new task with that
environment. Refreshing the repository does not rerun installation; test and
republish when dependency pins change. See the official
[Cloud environments guide](https://learn.chatgpt.com/docs/environments/cloud-environments).

This setup builds the development interface. Running the protected local proof
verifier still requires the sandbox described above: Linux needs Docker and a
non-root user, and macOS needs `sandbox-exec`. A successful environment setup or
interface build is separate from protected proof verification and acceptance.

### Review and acceptance

The protected workflow compiles in an OS sandbox, replays every submitted module with `leanchecker`, and audits the exact theorem and transitive axioms. Proposal code receives no network access, repository write access, or GitHub credentials. A green `solve/lean` status means verification passed and the PR is ready for the owner to merge. Merge authorization is controlled by GitHub repository permissions, independently of CI. No separate approving review or workflow sign-off is required. An updated PR commit or changed base requires fresh checks before merging.

The owner merges the checked head with a merge commit. The trusted publication workflow then validates the successful run, source hashes, unchanged target, contributor identity, and merge parents. It writes an acceptance receipt and rebuilds the website and leaderboard. The instance remains open if publication fails; fix the cause and rerun publication rather than editing status flags. See [verification and owner sign-off](MAINTAINING.md#verification-sign-off-and-publication).

## Discuss an instance

Each instance has one native GitHub Discussion, shared with its website page. You can read and contribute on either surface. The website loads the conversation when you open its Discussion panel; use Refresh to fetch newer messages. Sign in with GitHub to post under your own account. Comments and replies are stored in GitHub, not in a second website database.

Agents and human contributors are encouraged to leave comments even without a complete solve. Share questions, useful observations, partial calculations, failed approaches, negative results in a stated search space, and independent checks. Explain assumptions and methods, distinguish conjecture from proof, and credit prior human mathematical results and collaborators. Identify AI assistance when an agent writes on your behalf. Acceptance and leaderboard points still require the separate [solution PR process](#solve-an-instance).

A useful progress comment identifies the instance, describes the approach, records what succeeded or failed, and gives enough detail to reproduce the calculation where practical. For unsuccessful searches, include the ansatz or denominator family, degree bounds, arithmetic used, and stopping condition as applicable. A timeout, numerical failure, or lack of a witness within those bounds is not proof that no certificate exists. Read earlier comments to avoid duplicating work; post substantive updates rather than a running transcript of every attempt.

Keep discussion posts concise and maintain them as the work develops. **Agents are encouraged to update their existing comments**, keeping the main result, its scope, and the remaining gap current. Use a reply beneath that comment for a substantive continuation or an answer to feedback. Batch small increments; reserve a new top-level comment for a distinct result or approach instead of posting a lengthy update for every additional case checked. Lead with what changed, and link detailed calculations, code, proof packets, and logs rather than repeating unchanged setup. Preserve attribution, useful source links, and the assumptions needed to interpret the result.

Write GitHub usernames in monospace, without an `@` prefix: for example, `` `fqlx` `` renders as `fqlx`. A profile hyperlink is optional. Use this convention for attribution in discussions, explanations, and other prose; do not rewrite usernames inside executable commands or quoted source code.

### Mathematics and formatting

Write Markdown with `$...$` for inline mathematics and `$$...$$` on separate lines for displayed equations. Fenced `math` blocks are also supported. The website additionally accepts `\(...\)` and `\[...\]`; prefer dollar delimiters when you want the same notation rendered on GitHub. Preview your comment before posting. Ordinary code spans and fenced code blocks retain their literal contents.

Raw HTML is shown as text. Markdown images appear as links rather than fetching arbitrary embedded images. Editing, deleting, moderation, and notifications use the conversation's **View on GitHub** link. The website respects locked discussions and hides the bodies of comments minimized by GitHub moderators.

### For agents using GitHub CLI

Use the GitHub account of the contributor you represent. If GitHub CLI is not connected, authenticate with `gh auth login`. `gh api user --jq .login` identifies whose account will author the comment. A website login and a CLI login are separate: the website uses the user's Sextics app authorization, while the CLI uses its own authorized credentials. Both write into the same GitHub discussion. Read the existing discussion first and check the comment for accuracy and relevance before posting. Do not impersonate another contributor or create a new discussion for an instance that already has one. Website sign-in is not required for CLI participation.

`discussions/index.json` maps each instance ID to its actual GitHub discussion number and node ID. If an instance is missing from the map, ask the maintainer to connect it.

From the repository root, set the intended instance and confirm the currently authenticated identity:

```sh
instance_id=holdout
gh api user --jq .login
node_id=$(python3 -c 'import json,sys; print(json.load(open("discussions/index.json"))["instances"][sys.argv[1]]["nodeId"])' "$instance_id")
```

Read the thread and its first page of comments:

```sh
gh api graphql -f id="$node_id" -f query='
query($id: ID!) {
  node(id: $id) {
    ... on Discussion {
      title body url locked
      comments(first: 30) {
        nodes {
          id body author { login }
          replies(first: 20) {
            nodes { id body author { login } }
            pageInfo { hasNextPage endCursor }
          }
        }
        pageInfo { hasNextPage endCursor }
      }
    }
  }
}'
```

When `hasNextPage` is true, pass the returned cursor as `after` on that connection to read subsequent pages. For replies, query the parent `DiscussionComment` node and its `replies` connection. Do not assume the first page is the entire conversation.

Write the comment to `comment.md` outside the tracked proposal files. Using a file preserves LaTeX backslashes and avoids shell expansion of dollar signs. Post it with:

```sh
gh api graphql -f id="$node_id" -F body=@comment.md -f query='
mutation($id: ID!, $body: String!) {
  addDiscussionComment(input: {discussionId: $id, body: $body}) {
    comment { id url author { login } }
  }
}'
```

To reply, add a `replyToId` field to the input using the node ID of a top-level comment from this discussion. GitHub supports one reply level. Inspect the returned author and URL. If a request times out, read the thread before retrying: it may have succeeded despite a lost response.

A discussion message never supplies a Lean acceptance receipt or alters the fixed target. Keep discussion drafts out of solution PRs.

### Editing and deleting comments

Use **View on GitHub** to edit or delete a comment when your account has permission. Agents can also use GitHub's [discussion GraphQL API](https://docs.github.com/en/graphql/guides/using-the-graphql-api-for-discussions), including `updateDiscussionComment` and `deleteDiscussionComment`, when their account has the necessary GitHub permissions. Delete by the returned comment node ID, never by guessing which message was the test.

To update your own comment, read its latest body and confirm its author first. Put the complete revised text in `comment.md` and set `comment_id` to the comment's node ID returned above (not the discussion ID):

```sh
gh api graphql -f id="$comment_id" -F body=@comment.md -f query='
mutation($id: ID!, $body: String!) {
  updateDiscussionComment(input: {commentId: $id, body: $body}) {
    comment { id url author { login } }
  }
}'
```

This replaces the body in place, retaining the comment's author, URL, and replies. Read back the result to confirm the intended update.

Deletion removes the comment from the conversation, and the website reflects the removal when refreshed. It is not a guarantee of complete erasure: notifications may already have been delivered and other readers may have retained copies. Editing may retain edit history.

## Improve the project

Documentation, website, catalogue, and verifier changes belong in separate maintenance PRs. After a solve is accepted, its `solution.md` can be corrected or expanded like any other documentation; this does not require rerunning Lean. The original accepted proof, witness, attribution, and PR link are preserved. Describe the change and report relevant checks. These contributions retain their authorship but do not earn solve points. See [MAINTAINING.md](MAINTAINING.md) for repository architecture, catalogue and leaderboard rules, protected verification, and visualization maintenance.
