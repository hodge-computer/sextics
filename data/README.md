# Mathematical records

`catalogue.json` lists stable instance IDs in navigation order. Each existing `data/<id>/` folder contains the exact target `instance.rec`, prospective motivation `why.md`, and a context and related-instance index in `provenance.json`.

A solve PR adds `proof.json`, `Solution.lean`, `solution.md`, optional `witness.json`, and optional flat Lean helpers to that same folder. It cannot edit existing files. See [the full proposal specification](../CONTRIBUTING.md).

After a solve is merged, the publisher adds `acceptance.json` containing its contributor, original PR number/link, and acceptance date. `scripts/build-content.py` reads these records and any exported denominator in `witness.json` to generate status and credit. The website renders the current repository contents; proof verification belongs to CI before merging.

`.rec` files use YAML. Exact polynomial expressions use the variable order `X0, X1, X2, Y0, Y1, Y2`, rational coefficients, and `**` for powers. These files contain no rendering settings, display LaTeX, or expanded coefficient lists. The build derives coefficients from the exact expressions. Saved planes, cameras, and display divisors belong in `slices/`; curated typesetting belongs in `assets/atlas-presentation.json`. An accepted target must not be silently repurposed for another `(F,q,A)`.

## Instance descriptions

Keep `why.md` separate from the solution narrative and ongoing discussion. Open instances use the established results available now; solved instances use the established context immediately before their own solution. Do not include discussion reports or links, the instance's own proof, or later breakthroughs in a solved instance's motivation. See the [curation policy](../MAINTAINING.md#catalogue-curation).

## Editing an accepted explanation

Edit `solution.md` directly and rebuild the content. The site uses its current text. This does not change the accepted proof, contributor credit, or PR link, and does not require another Lean run. The original submission is retained in Git history. Changes to Lean sources, targets, proof manifests, or witnesses belong in maintenance PRs and trigger fresh CI verification. Preserve the original attribution in `acceptance.json`.

## Generated files

The website build writes its index, per-instance JSON, and rendered explanations to `assets/atlas/`. This directory is disposable build output, including polynomial coefficient arrays; do not commit it. For authorized source maintenance, rebuild and validate:

```sh
python3 scripts/build-content.py
python3 scripts/validate-records.py
python3 scripts/check-content.py
```

## Structured frontier checks

Ten structured targets include `checks.json`, reproducible with SageMath:

```sh
sage -python scripts/audit-frontier.py
```

The script reads the exact `.rec` statements and checks their parity, degrees, coordinate reflections, elementary split Euler conditions,
Hessian symmetrizers, and diagonal symmetry characters. It also checks the
specific old-denominator obstruction for `quadric-contact-broken`.

For these targets, reduction modulo five has partial derivatives equal to the
six fifth powers, possibly permuted. The projective special fiber is therefore
smooth. Properness of the projective singular locus implies smoothness in
characteristic zero. In both fibers the Jacobian ideal is a complete intersection
of six quintics, with the same Hilbert function. Its graded quotients over the
local ring at five are consequently free, so a nonzero reduced target class
cannot have been zero over the rationals. Scalar extension gives the same
conclusion over the complex numbers. This extra constant-rank argument matters:
nonzero reduction alone does not generally prove characteristic-zero
nonmembership in an ideal.

The symmetry screens exclude only the specified constructions. They do not
classify all automorphisms, polynomial maps, contact divisors, or possible
certificates. Known geometric existence is recorded separately in each
`why.md` with its theorem reference. None of these curation checks awards a
solve or replaces the protected Lean acceptance workflow.
