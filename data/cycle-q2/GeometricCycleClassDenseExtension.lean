import Mathlib.Topology.Separation.Hausdorff

/-!
# Dense-open specialization of locally identified cycle-class values

For fixed cohomology fibers in a local trivialization, the target vector
space is Hausdorff. Two continuous cohomology-class representatives agreeing
on a dense open then agree throughout the closure, including special fibers.
This formalizes the *topological separatedness* part of cycle-class
specialization. It does not construct continuous cycle-class maps or
trivializations of an actual Gauss-Manin local system; those are substantive
remaining geometric obligations in cycle-q2.
-/

set_option autoImplicit false

namespace CycleQ2CycleClassDenseExtension

variable {S H : Type*} [TopologicalSpace S]
variable [TopologicalSpace H] [T2Space H]

/-- Equality of continuous class representatives extends across every
specialization lying in the closure of the dense construction locus. -/
theorem eq_of_dense_open
    (U : Set S) (hU : Dense U)
    (cycle projector : S → H)
    (hc : Continuous cycle) (hp : Continuous projector)
    (hEq : Set.EqOn cycle projector U) :
    cycle = projector :=
  Continuous.ext_on hU hc hp hEq

/-- The class identity holds at every special parameter, without assuming
the original dense open intersects the new parameter locus. -/
theorem eq_at_specialization
    (U : Set S) (hU : Dense U)
    (cycle projector : S → H)
    (hc : Continuous cycle) (hp : Continuous projector)
    (hEq : Set.EqOn cycle projector U) (s : S) :
    cycle s = projector s := by
  exact congrFun (eq_of_dense_open U hU cycle projector hc hp hEq) s

/-- The same identity holds after *any* parameter map. -/
theorem eq_after_base_change
    (U : Set S) (hU : Dense U)
    (cycle projector : S → H)
    (hc : Continuous cycle) (hp : Continuous projector)
    (hEq : Set.EqOn cycle projector U)
    {T : Type*} (b : T → S) (t : T) :
    cycle (b t) = projector (b t) :=
  eq_at_specialization U hU cycle projector hc hp hEq (b t)

/-- Specializing a constant cohomology class does not change that class,
provided the actual family of classes is continuous on the chosen model. -/
theorem constant_of_dense
    (U : Set S) (hU : Dense U)
    (cycle : S → H) (c : H)
    (hc : Continuous cycle)
    (hEq : ∀ s ∈ U, cycle s = c) :
    ∀ s : S, cycle s = c := by
  intro s
  apply eq_at_specialization U hU cycle (fun _ : S => c)
    hc continuous_const
  exact hEq

end CycleQ2CycleClassDenseExtension

#print axioms CycleQ2CycleClassDenseExtension.eq_after_base_change
#print axioms CycleQ2CycleClassDenseExtension.constant_of_dense
