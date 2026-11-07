ACTUAL SYMMETRIC-SEXTIC CONTACT SPAN

The first48 obstruction-functional Taylor rows on the actual lambda=1 contact
curve have rank48. Both that conclusion and smoothness of the contact curve
now have independent exact-rational replay, without a large finite-algebra or
Groebner-basis computation. See CONTACT_SPAN_INTERPRETATION.txt for the precise
mathematical statement, canonical-residue identification, normal-bundle check,
generic-lambda implication, and remaining unproved formal endpoint.

MINIMAL REPLAY
==============
Required package: python-flint==0.9.0. The exact checkers do not use Arb,
NumPy, SciPy, floating-point rank, root finding, or the discovery scripts.
They find the prior assets in ../../research_contact in a delivered package,
or ../../proof_attempt4 in the development workspace.

From this directory run:

  python check_contact_jet_witness.py
  python check_contact_curve_smoothness.py

The first reconstructs exact residual series and proves the actual48-minor
invertible with a Neumann defect at most2^(-981). The second proves the
degree-six smoothness minor invertible throughout the prior contact ball,
with a defect at most2^(-94). Receipts include the exact witness/input hashes.

ESSENTIAL FILES
===============
exact_target_contact_jet_witness.json
check_contact_jet_witness.py
contact_jet_rational_replay.json
contact_jet_rational_replay.log
contact_curve_smoothness.json
check_contact_curve_smoothness.py
contact_curve_smoothness_rational_replay.json
contact_curve_smoothness_rational_replay.log
CONTACT_SPAN_INTERPRETATION.txt

The parent folder's actual_target_jacobian.py/receipt binds G and the reflected
protected F and A directly to the original instance, and checks the complete
12-dimensional Jacobian ideal. The differential-form/source binding is a
separate remaining obligation described in generic_fiber_current_route.txt.
ContactResidueAnnihilator.lean supplies the exact algebraic annihilation
identities used in the interpretation.

REGENERATING APPROXIMATION DATA
==============================
This optional discovery stage uses python-flint, NumPy, and SciPy. It is not
needed to verify the saved witnesses.

  python exact_target_contact_jets.py --digits 800 --order 47
  python contact_curve_smoothness.py

The800-digit run refines the old contact, constructs the finite jets using
Arb interval arithmetic, and exports exact dyadic approximations. The rational
checker derives its own bounds and does not trust the Arb determinant.
exact_target_contact_jets_47_800.json/log and contact_curve_smoothness.log record
that generation stage. The earlier400-digit run is historical discovery data.

fermat_contact_seed.py/.json is a separate unsuccessful small modular seed:
its contact Jacobian has rank42 and its quadratic obstruction forms vanish.
It supplies no generic lift, does not support an unrestricted no-go claim,
and is not used by either successful exact-rational verification.

STATUS
======
These calculations close the actual-target contact smoothness and finite-jet
source-image checks. They do not evaluate a full source trace, construct the
required regular rational current, or prove the protected HasCertificate
statement in Lean. The geometry-to-rational-current theorem and formal
verification of the finite witnesses remain substantive formal obligations.
