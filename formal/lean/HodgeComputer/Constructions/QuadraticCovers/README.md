# Quadratic cover algebra, Laurent jets, and rational cover residues

Target-independent algebraic machinery for rational 1-forms arising as traces from a quadratic extension over a rational function field, extracted from `benediamond`'s [`symmetric-sextic-residual`](../../../../../data/symmetric-sextic-residual/solution.md) construction.

Import the individual modules; declarations lie in the namespace `QuadraticCovers`.

| Module | Mathematical role |
| --- | --- |
| `PairAlgebra` | Polymorphic quadratic quotient algebra `PairAlg R = R[W] / (W^2 + bW * W + cW)`, the two-branch Euler trace cancellation identity `PairAlg.eulerTr_div`, and the explicit 5×5 quadratic–cubic Sylvester resultant `syl5` and `syl5Pair`. |
| `LaurentJets` | Dual numbers `Dual R`, recursive Hensel power-series root `quadRootSeries` of `r^2 + b * r + c = 0`, Laurent valuation predicate `HasValGe`, polynomial embeddings `evalT` and `evalInvT`, and packaged leading-term (`ValLead`) and two-term (`ValDual`) jet predicates. |
| `RationalCoverResidues` | Pure-ring 4×4 Schur complement `det_J_fib_schur`, division-free degree-4/degree-3 quadratic remainders `remDeg4` / `remDeg3`, 5-point Lagrange interpolation `interp4` with scaled Laurent valuation bounds (`HasValGe.interp4_scaled`), simple-pole residues, and functorial base change `mapRatFunc` preserving regularity and finite/infinity residues. |

Build all modules with:

```bash
lake build HodgeComputer.Constructions.QuadraticCovers.PairAlgebra \
  HodgeComputer.Constructions.QuadraticCovers.LaurentJets \
  HodgeComputer.Constructions.QuadraticCovers.RationalCoverResidues
```
