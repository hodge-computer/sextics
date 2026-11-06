# Sextic fourfolds with an involution

These chapters develop the generalized Hodge conjecture for the involution-invariant middle cohomology of a smooth sextic fourfold. The certificate equation gives an explicit way to construct and check divisor support. Geometric arguments can establish the same support directly, and the two approaches often explain one another.

The case of a Zariski-general globally \(Y\)-even sextic remains open. The chapters distinguish family-wide results from constructions for particular targets. The atlas presents concrete instances and, where a construction is available, explains how it works.

## Reading order

The intended reader knows basic algebraic geometry, differential forms and Hodge decomposition. For constructing a certificate, start with Chapters 1, 2 and 5. For the geometric approach and its scope, continue through Chapters 3, 3A, 3B and 4. Foundational results from the literature are cited where they enter; the accompanying arguments explain their application to this problem.

| Chapter | Purpose |
| --- | --- |
| [1. From invariant cohomology to rational certificates](#technical-information/certificates) | The geometric target, key equation, Euler normalization, support, pole multiplicity and coefficient descent |
| [2. Explicit constructions](#technical-information/explicit-constructions) | Cofactor transport, cubic-surface target spanning, finite-cover integration, and moving cubic maps |
| [2a. Binary blocks](#technical-information/binary-blocks) | Universal binary contact, target spanning and assembly for arbitrary same-parity binary blocks |
| [3. Geometric support](#technical-information/geometric-support) | Gysin maps, finite-group projectors, Fano and surface fibrations, and supported projectors in families |
| [3a. Split sextics and K3 surfaces](#technical-information/split-and-k3) | Elliptic companions, quotient resolutions, polarized splitting and the Clifford/Kuga–Satake support argument |
| [3B. Weighted threefolds and two-reflection sextics](#technical-information/weighted-threefolds) | Voisin's Fano-extension method, Abel–Jacobi variation, monodromy and all-target two-reflection support |
| [4. The known locus and the open frontier](#technical-information/known-locus) | Family and representation dimensions, paired-sign surface quotients, all-target chain support and the generic frontier |
| [5. Computing and checking certificates](#technical-information/computation) | Complete coefficient systems, numerical discovery, exact identities and Lean acceptance |

An explicit field supplies a primitive off a divisor; a geometric support supplies a numerator problem. Finite-group projectors identify the cohomology reached by each quotient or cover. Chapter 3B combines two existing Fano-supported reflection sectors with a weighted-threefold correspondence for their missing simultaneous negative sector. It proves all-target support whenever one additional reflection exists in each parity block. Earlier strict formulas and bounded support constructions retain their computational content even on families covered by this existence theorem. Chapter 4 compares the resulting coefficient families and representations with the transcendental parts a general theorem must still serve.

## Notation

We use \(Z=(X_{0},X_{1},X_{2},Y_{0},Y_{1},Y_{2}), \tau (X,Y)=(X,-Y)\), and \(X=V(F)\subset \mathbb P^{5}\) for the fourfold. “\(Y\)-even” refers to total \(Y\)-degree, unless individual coordinate reflections are explicitly stated. The numerator \(A\) is \(Y\)-odd because the projective volume form changes sign under \(\tau \). In the general certificate contract, \(n\) is the ambient projective dimension and \(d=\deg(F)\); here \(n=5,d=6\). The target parameter \(q\) is distinct from the unrestricted denominator degree \(\deg(D)\).

## Reading the atlas

Each instance specifies \((F,q,A)\). “Why this instance matters” describes the target; the solved badge opens its construction explanation. A construction for one instance does not establish a general family theorem. Likewise, failure in a restricted denominator search does not rule out other certificates.

Acceptance requires a checked Lean theorem for the protected instance statement, including when mathematical existence is already known geometrically. Chapter 5 explains the distinction and the passage to that theorem.
