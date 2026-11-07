# Independently checked compact-current upgrade

The three ZIPs preserve the existing source and character. They add actual operator coefficients and the fully evaluated eight-stage source, not a new target. The sufficient closure is G_P[f]+G_U[h]=g, where G are ACTION matrices, not source matrices. The exact 3x3 first-order reformulation is documented in FIRST_ORDER_SYSTEM.md.

All actual moving-section flux terms are retained. The generic g is the full 44-input derivative recipe, not just c1C1+c2C2 or any sample constants. Independent local checks rebuilt the parent circuit byte-identically, verified generic literal Xi identities, all coefficient weights, and freshly reproduced all eight source stages with a second evaluator. The full generic source has not been derivative-expanded into an ordinary DAG. No closure or certificate is claimed.

Use these completed inputs for construction rather than rederiving the finite/infinity connections or assigning arbitrary source values. The original q2 certificate still requires full physical lift/trace and F^3Q verification.
