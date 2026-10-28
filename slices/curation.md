# Saved real slices and cameras

Each `slices/<instance-id>.json` records the phase choices, orthonormal real four-plane, mesh, and camera used to visualize that instance. This is the sole source of those settings; the content builder copies them into browser records. The saved plane must match the selected mesh manifest. The projected box is fixed at ±10, and x-ray reach is 2.0.

A camera has three fields: a unit quaternion `orientation` in `[x,y,z,w]` order, a `distance`, and a three-coordinate `center`. The quaternion maps the camera's right/up/back axes into world coordinates and is the sole saved orientation. Exploration and background parallax apply rotations directly to it; reset restores the saved pose.

Normalize a new saved camera by measuring the projected triangle silhouette in a
320×200 viewport with the renderer's field of view. Choose the distance for 32%
coverage, or a farther distance if needed to keep every projected vertex within
90% of the viewport extent; then increase that distance by 10%. Preserve the
chosen quaternion and center. Coarsen replacement meshes with the adaptive
procedure in MAINTAINING.md and inspect the result before selecting it.

Meshes sample the real section obtained by intersecting the chosen four-plane with the unit sphere and the sextic, then stereographically projecting into three dimensions. Their positions and normals are floating-point presentation data. They do not prove smoothness, topology, or certificate validity.

Validate finite values, normals, coordinate and index bounds, edge lengths, and polynomial residuals when replacing a mesh. `scripts/validate-records.py` checks consistency between the current records, saved slices, and mesh manifests. A finite grid can miss sufficiently thin features. Camera and slice choices are aesthetic decisions, independent of the mathematical target.

Denominators are evaluated directly at each pixel, independently of the geometric mesh. Compact formulas and slice-specific factorizations can be supplied through `slices/divisors/<id>.json`; see MAINTAINING.md. A factorization restricted to a saved plane must be regenerated if that plane or its coordinate phases change. Open instances have no displayed denominator.

Klein · rational Piola trace keeps `X0 = 0`, where `D = X1^18 * X2^12`.
Sample new planes within that hyperplane to retain real divisor curves.
Making `F` real-valued alone does not ensure that `D = 0` has real codimension one.

The homepage uses its separately saved Contact cone view in `home.json`. The Contact cone atlas entry uses `contact46006.json`.

Equal-sextic targets share the same geometric section and camera: the two Fermat targets, the two cross-block Two ties targets, the coupled Fano reflection and its complementary-character target, and the cyclic triple cover and its complementary-character target. Their accepted denominators, when available, are evaluated independently. Special sections used to expose repeated-factor divisors are checked by the exact `sliceIdentity` mechanism described in MAINTAINING.md.

Off-block tie and One tie share the latest One tie section and camera. Off-block tie now evaluates its submitted denominator directly; its previous square-root display formula was valid only on its former section. A common section need not expose real divisor curves for every certificate on the same sextic.

The twelve central holdout targets share one four-plane and camera with `Y0/X0 = 23i/20` and `Y1/X1 = 3i/4`. These ratios allow the pole-two target's exact norm divisor to be displayed. Changing the camera is unrestricted; changing the saved plane requires re-exporting the formula, and changing the ratios requires a new extraction. One reflection's residual sector uses a section with a fixed ratio between `Y1` and `Y0`, avoiding repeated-factor junctions in its divisor highlights. Its transverse sector has no exported denominator and uses a separate unrestricted four-plane. These choices do not change the exact instances or accepted certificates.
