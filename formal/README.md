# The formal acceptance contract

For reusable constructions and worked applications, see the [technique guide](TECHNIQUES.md).

The target is existence of a rational-vector-field certificate, with no bound on the denominator degree. Constructive and nonconstructive proofs establish the same statement for the specified data.

For arbitrary natural numbers `n`, `d`, and `q`, let `R = ℂ[z₀,…,zₙ]`. The contract requires `F ≠ 0`, `F` homogeneous of degree `d`, and `A` homogeneous of integer degree `d(q+1) − (n+1)`. It asks for a nonzero homogeneous denominator `D`, numerators `N₀,…,Nₙ`, and a polynomial `Q` such that:

- `D` is relatively prime to `F`.
- Each `Nᵢ` is homogeneous of integer degree `deg(D) + dq − n`.
- The rational field `vᵢ = Nᵢ / D` satisfies `F^(q+1) ∣ A − q·dF(v) + F·div(v)` in the localization obtained by inverting polynomials relatively prime to `F`.

Integer homogeneity means that every monomial with nonzero coefficient has the specified degree. The zero polynomial is homogeneous of every integer degree; a negative degree permits only zero. There is no independent homogeneity or nonvanishing condition on `Q`.

The catalogue specializes to `n=5`, `d=6`, coordinates `X0,X1,X2,Y0,Y1,Y2`, and `q∈{1,2}`. Its targets have `F(X,−Y)=F(X,Y)` and `A(X,−Y)=−A(X,Y)`. The general contract imposes no parity requirement on the field.

## A finite algebraic witness

Define the polynomial

```text
E = A D² − q D Σᵢ Nᵢ ∂ᵢF
    + F (D Σᵢ ∂ᵢNᵢ − Σᵢ Nᵢ ∂ᵢD).
```

Since `D` is invertible in the relevant localization, a witness for the equation is the exact polynomial identity `E = F^(q+1) Q`. A strict certificate has `E=0`. This cleared identity, together with homogeneity and denominator admissibility, is the constructive checker interface. The theorem `localization_identity` in `HodgeComputer/Verify.lean` establishes the bridge to the rational-vector-field statement.

## Protected verification

`formal/lean/HodgeComputer/Verify.lean` defines `HodgeComputer.Verify (n := n) F A d q D N Q` and the existential `HodgeComputer.HasCertificate F q A` over complex coefficients. `HasCertificate` uses `F.totalDegree`; it takes only `F`, `q`, and `A` as explicit inputs. The implicit `n` is inferred from `F` and `A`, whose type is `HodgeComputer.AmbientPoly n = MvPolynomial (Fin (n + 1)) ℂ`. The witness checker retains an explicit degree `d`, established by its nonvanishing and homogeneity fields. `Verify.hasCertificate` uses those fields to identify `d` with `F.totalDegree`. The localization identity justifies the cleared equation. The shared contract imposes no denominator-degree bound or extra parity condition on the witness.

The verifier generates a protected exact target from the base branch's record. Contributors prove its existential statement and, when exporting a JSON witness for display, an additional theorem about those exact witness polynomials. The protected pipeline compiles the source in isolation, replays its declarations with the kernel checker, and audits the statement and axioms. Allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.

A rational-coefficient identity transfers to complex coefficients, but denominator admissibility over the complex numbers must also be established. Do not infer complex coprimality merely from rational irreducibility. Nonconstructive proofs are allowed when they establish the same protected existential theorem.

The Lean project pins its toolchain and mathlib manifest. Instance-specific proofs belong to each instance's existing data folder and first enter through its solve PR. Reusable, target-independent machinery may be placed under `formal/lean/HodgeComputer/Constructions/` either directly in the solve PR that uses it or in a separate maintenance PR. CI checks the proof (and any companion library modules) before the owner merges it. The publisher records contributor credit in `acceptance.json`; the website renders the current repository contents. See [the proposal specification](../CONTRIBUTING.md) and [verification workflow](../MAINTAINING.md#verification-sign-off-and-publication).

## Reusable constructions

The shared library under `formal/lean/HodgeComputer/` is the Lean counterpart of the mathematical book: organized, reusable statements with explicit hypotheses and concrete applications. Four core modules (`Verify`, `Sextic`, `CertificateOperations`, `CoordinateChanges`) define the protected contract and elementary certificate operations; reusable proof machinery lives in themed packages under `formal/lean/HodgeComputer/Constructions/`.

A new shared construction should do substantive proof work in at least one completed solve, build without warnings, and carry clear attribution to the constructions it came from. Keep exploratory calculations, unsuccessful searches, and target-specific closure arguments outside the shared library. See the [technique guide](TECHNIQUES.md) for the complete index of shared packages, their hypotheses, and their accepted applications.
