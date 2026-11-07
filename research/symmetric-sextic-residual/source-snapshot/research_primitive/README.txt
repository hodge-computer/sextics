SYMMETRIC SEXTIC: EXACT RATIONAL-PRIMITIVE TRANSPORT
Updated 2026-11-07 UTC

FULL TARGET STATUS: UNPROVED
RATIONAL PRIMITIVE EXISTENCE: UNPROVED

This update formalizes the exact equation a relative rational primitive must
satisfy, constructs its affine residue current, and proves legal polynomial
clearing from it. It does not construct that primitive. It also does not yet
assemble these affine identities into the original homogeneous certificate.
No Solution.lean, new axiom, admitted proof, or unconditional existence claim
has been introduced. The protected symmetric-sextic-residual F/A at q=1
are unchanged.

WHAT THE SIX NEW MODULES PROVE

The physical affine chart, in coordinate order (lambda,b,c,d,v), is

  X = (1+v, 1-v, b),
  Y = (c+lambda*v, c-lambda*v, d).

Write H = f(lambda,b,c,d,v^2), where f is the actual raw weighted equation,
and P = b*d*(1-u)*(c^2-lambda^2*u). The transformed source is

  A_H = 4*v*P(lambda,b,c,d,v^2).

1. WeightedPrimitiveTransportCore.lean binds H and A_H to the protected F/A,
   proves the normal square-cover chain rule, and computes the exact residue
   coefficient

     rho = 2*(f_u*P_u - f_uu*P)/f_u^3.

   All expressions in the function field use u=v^2. If G=f/ell is the monic
   equation and R=2P/ell^2 its source, the code proves that the monic residue
   expression equals this raw expression; the normalization cancels exactly.

2. SymmetricAffinePrime.lean proves that this H is irreducible. It is monic
   of degree six in b; setting lambda=c=d=0 gives

     b^6 + 2 + 30*v^2 + 30*v^4 + 2*v^6.

   The coefficient polynomial has a simple zero at v=i, so the section is
   Eisenstein at v-i. Monic specialization lifts irreducibility to H.

3. SymmetricAffineField.lean constructs B=C[lambda,b,c,d,v]/(H) and its actual
   fraction field K. At (0,0,0,0,i), H=0 and H_v=-48i. Thus H does not divide
   H_v, the normal is nonzero in K, and the denominators v and f_u are also
   nonzero there. These facts are proved, not supplied by a caller.

4. WeightedPrimitiveTransport.lean uses the repository's constructed
   canonical tangent derivations E_lambda,E_b,E_c,E_d. It proves their
   compatibility with the implicit weighted derivatives through u=v^2.
   From three coefficients satisfying

     E_b(beta_0) + E_c(beta_1) + E_d(beta_2) = rho,

   it explicitly constructs w=(0,-H_v*beta_0,-H_v*beta_1,-H_v*beta_2) and
   proves the exact weighted-divergence equation. The zero lambda component
   is valid even when the coefficients depend on lambda. The generic
   theorem permits a finite field extension; normalized trace descends the
   current before clearing its polynomial denominators.

5. SymmetricAffineJacobian.lean binds the polynomial derivative matrix of
   the full chart (a,lambda,b,c,d,v), proves det(J)=+4*a^5*v, proves F pulls
   back to a^6*H, and verifies the complete projective source coefficient

     A_pullback * a * det(J) / F_pullback^2 = A_H / H^2   (a != 0).

   This is a formal coefficient identity. It is not by itself a theorem
   about transport of a differential-form primitive or a final certificate.

6. SymmetricPrimitiveEndpoint.lean instantiates the construction with this
   actual quotient field. RelativePrimitive contains exactly three rational
   functions and a proof of the displayed relative derivative equation.
   Theorem clear_relative_primitive gives D,N_v,N_lambda,N_b,N_c,N_d,Q with

     D != 0,  IsRelPrime H D,
     N_v*H_v + sum N_i*H_i = A_H*D,
     residueDivNum(D,N) = H*Q,
     A_H*D^2 - D*(N_v*H_v + sum N_i*H_i) + H*residueDivNum(D,N) = H^2*Q.

   The module DOES NOT prove Nonempty RelativePrimitive.

The corresponding relative two-form convention is

  beta = beta_0 dc wedge dd - beta_1 db wedge dd + beta_2 db wedge dc.

Its desired absolute primitive is -d(lambda) wedge beta. A normal-first
Poincare-residue convention can negate rho; negating beta reconciles that
convention. The polynomial/current identities themselves have fixed signs.

WHAT THE EXISTENCE PROOF STILL REQUIRES

The existing contact-span argument is a mathematical route to the zero map

  H^3_dR(T/k)^- -> H^3(Omega^bullet_{k(T)/k}).

It is not a theorem that all rational three-forms are exact. Formalizing
this route requires the actual contact correspondence and its comparison
with the weighted residue functional, and then algebraic vanishing off the
support. The actual 48-jet certificate remains an external exact-arithmetic
calculation, not a Lean-checked matrix/rank witness.

An audit of pinned openai/math sources found substantial genuine Hodge,
projective de Rham comparison, Poincare-duality, and singular support
foundations. It did not find the required contact Abel-Jacobi/residue
identification or the algebraic support-to-function-field implication.
Those external sources use Lean 4.34.1 and a different mathlib revision;
they were statically audited but were NOT compiled or imported by any of
the six modules above. Their existence does not finish the target.

The direct algebraic route gives 48 explicit local principal-part classes
from the inverse contact-jet matrix. These are not automatically globally
closed scalar trace weights. The included exact countermodel shows that
full trace rank plus full jet rank alone is insufficient for that shortcut.
Neither route produced the missing beta coefficients in this update.

Once an actual primitive is proved, the remaining affine-to-homogeneous
transport still must be assembled with the earlier regular/Euler clearing
endpoint. The existing protected endpoint is

  SymmetricRegularCurrent.certificate_iff_regular_game_exists,

and SymmetricRegularCurrent.RegularGameExists remains unproved.

VALIDATION

All six new modules compiled under Lean 4.33.1 with the unchanged mathlib
revision 0df444a360eaa60ab8c11dca51a86af692955474. An axiom audit checked all
51 public theorems and found only propext, Classical.choice, and Quot.sound.
Every one of the six module objects passed independent leanchecker replay
against its pinned imported environment. Imported dependencies were not
replayed again from an empty environment. No new custom axiom, sorry,
admit, or native_decide occurs in the checked sources.

An independent mathematical review checked the exact target, coefficient
normalization, derivative indices, prime/domain proof, current, and scope.
The separate Python source/Jacobian check agrees with the Lean identities.

REPLAY

The combined packet keeps our Lean modules and objects at its top level.
This update's research and reports are under research_primitive/. Previous
contact evidence and computations are retained in their original folders.
The packet's module list now has 69 modules; this update replayed the six
new modules. The prior 63 modules and their validation receipts are retained.

With Lean 4.33.1 and the pinned sextics checkout available:

  python3 compile_transport_dependencies.py --repo /path/to/sextics
  python3 audit_primitive_transport.py --repo /path/to/sextics

For source recompilation as well as replay, use the existing verifier:

  python3 verify_partial.py --repo /path/to/sextics --modules \
    WeightedPrimitiveTransportCore SymmetricAffinePrime SymmetricAffineField \
    WeightedPrimitiveTransport SymmetricAffineJacobian SymmetricPrimitiveEndpoint

The dependency builder compiles only missing, unchanged upstream sources.
The proof attempts and the external foundation source audit are separate:

  python3 research_primitive/direct/trace_closedness_counterexample.py
  python3 research_primitive/geometry/audit_openai_foundations.py --local-only

The latter replay unpacks and hashes explicitly labeled third-party source;
it is not a Lean compiler run. See geometry/external_foundations_replay.txt.

The protected input SHA256 is
  b57fe82288d74a788fd725ef24660c06a58c0bbf8430b82dd506db37aa4c9390.
The protected HodgeTarget.lean SHA256 is
  a51532e0442d72e8ce95d6728390fac0f719287d1cf20020701625bc1b5409d9.

All earlier work and large-checkpoint restoration links remain in this
packet. This update changes no large solver checkpoint and reports no new
full source trace or target certificate.
