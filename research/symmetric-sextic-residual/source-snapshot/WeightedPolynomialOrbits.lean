import WeightedPolynomialData
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace WeightedSupport.PolynomialModel

def IsCapped (e : Exponent) : Prop := ∀ i, e i < if i = 5 then 2 else 5

instance (e : Exponent) : Decidable (IsCapped e) := by unfold IsCapped; infer_instance

def weightedDegree (e : Exponent) : ℕ :=
  e 0 + e 1 + e 2 + e 3 + e 4 + 2 * e 5

def boxExponent (k : ℕ) : Exponent :=
  ![k / 1250 % 5, k / 250 % 5, k / 50 % 5, k / 10 % 5, k / 2 % 5, k % 2]

def encodeExponent (e : Exponent) : ℕ :=
  e 0 + 8 * e 1 + 64 * e 2 + 512 * e 3 + 4096 * e 4 + 32768 * e 5

def Canonical (minus : Bool) (e : Exponent) : Prop :=
  e 0 < e 1 ∨ e 0 = e 1 ∧ (if minus then e 2 < e 3 else e 2 ≤ e 3)

instance (minus : Bool) (e : Exponent) : Decidable (Canonical minus e) := by
  unfold Canonical
  infer_instance

def orbitBlock (degree : ℕ) (minus : Bool) (block : ℕ) : List ℕ :=
  ((List.range 250).filter fun k =>
    decide (weightedDegree (boxExponent (250 * block + k)) = degree ∧
      Canonical minus (boxExponent (250 * block + k)))).map
    (fun k => encodeExponent (boxExponent (250 * block + k)))

def orbitCodes (degree : ℕ) (minus : Bool) : List ℕ :=
  (List.range 25).flatMap (orbitBlock degree minus)

theorem boxExponent_capped (k : ℕ) : IsCapped (boxExponent k) := by
  intro i
  fin_cases i
  · change k / 1250 % 5 < 5; omega
  · change k / 250 % 5 < 5; omega
  · change k / 50 % 5 < 5; omega
  · change k / 10 % 5 < 5; omega
  · change k / 2 % 5 < 5; omega
  · change k % 2 < 2; omega

theorem boxExponent_complete (e : Exponent) (he : IsCapped e) :
    ∃ k < 6250, boxExponent k = e := by
  have h0 : e 0 < 5 := by simpa using he 0
  have h1 : e 1 < 5 := by simpa using he 1
  have h2 : e 2 < 5 := by simpa using he 2
  have h3 : e 3 < 5 := by simpa using he 3
  have h4 : e 4 < 5 := by simpa using he 4
  have h5 : e 5 < 2 := by simpa using he 5
  refine ⟨1250 * e 0 + 250 * e 1 + 50 * e 2 + 10 * e 3 + 2 * e 4 + e 5, by omega, ?_⟩
  funext i
  fin_cases i
  · change (1250 * e 0 + 250 * e 1 + 50 * e 2 + 10 * e 3 + 2 * e 4 + e 5) / 1250 % 5 = e 0
    omega
  · change (1250 * e 0 + 250 * e 1 + 50 * e 2 + 10 * e 3 + 2 * e 4 + e 5) / 250 % 5 = e 1
    omega
  · change (1250 * e 0 + 250 * e 1 + 50 * e 2 + 10 * e 3 + 2 * e 4 + e 5) / 50 % 5 = e 2
    omega
  · change (1250 * e 0 + 250 * e 1 + 50 * e 2 + 10 * e 3 + 2 * e 4 + e 5) / 10 % 5 = e 3
    omega
  · change (1250 * e 0 + 250 * e 1 + 50 * e 2 + 10 * e 3 + 2 * e 4 + e 5) / 2 % 5 = e 4
    omega
  · change (1250 * e 0 + 250 * e 1 + 50 * e 2 + 10 * e 3 + 2 * e 4 + e 5) % 2 = e 5
    omega

theorem decode_encode (e : Exponent) (he : IsCapped e) :
    decodeExponent (encodeExponent e) = e := by
  have h0 : e 0 < 5 := by simpa using he 0
  have h1 : e 1 < 5 := by simpa using he 1
  have h2 : e 2 < 5 := by simpa using he 2
  have h3 : e 3 < 5 := by simpa using he 3
  have h4 : e 4 < 5 := by simpa using he 4
  have h5 : e 5 < 2 := by simpa using he 5
  funext i
  fin_cases i
  · change (e 0 + 8 * e 1 + 64 * e 2 + 512 * e 3 + 4096 * e 4 + 32768 * e 5) / 1 % 8 = e 0
    omega
  · change (e 0 + 8 * e 1 + 64 * e 2 + 512 * e 3 + 4096 * e 4 + 32768 * e 5) / 8 % 8 = e 1
    omega
  · change (e 0 + 8 * e 1 + 64 * e 2 + 512 * e 3 + 4096 * e 4 + 32768 * e 5) / 64 % 8 = e 2
    omega
  · change (e 0 + 8 * e 1 + 64 * e 2 + 512 * e 3 + 4096 * e 4 + 32768 * e 5) / 512 % 8 = e 3
    omega
  · change (e 0 + 8 * e 1 + 64 * e 2 + 512 * e 3 + 4096 * e 4 + 32768 * e 5) / 4096 % 8 = e 4
    omega
  · change (e 0 + 8 * e 1 + 64 * e 2 + 512 * e 3 + 4096 * e 4 + 32768 * e 5) / 32768 % 8 = e 5
    omega

theorem orbitCodes_complete (degree : ℕ) (minus : Bool) (e : Exponent)
    (he : IsCapped e) (hd : weightedDegree e = degree) (hc : Canonical minus e) :
    encodeExponent e ∈ orbitCodes degree minus := by
  obtain ⟨k, hk, heq⟩ := boxExponent_complete e he
  unfold orbitCodes
  apply List.mem_flatMap.mpr
  refine ⟨k / 250, by simp only [List.mem_range]; omega, ?_⟩
  unfold orbitBlock
  apply List.mem_map.mpr
  have hk' : 250 * (k / 250) + k % 250 = k := by omega
  refine ⟨k % 250, ?_, by rw [hk', heq]⟩
  simp [List.mem_filter, List.mem_range, hk', heq, hd, hc]
  omega

theorem source_codes_nodup : sourceCodes.toList.Nodup := by decide +kernel
theorem q_target_codes_nodup : qTargetCodes.toList.Nodup := by decide +kernel
theorem hq_target_codes_nodup : hqTargetCodes.toList.Nodup := by decide +kernel

theorem source_degree_and_canonical : ∀ j : Fin 82,
    IsCapped (sourceExponent j) ∧ weightedDegree (sourceExponent j) = 5 ∧
      Canonical false (sourceExponent j) := by decide +kernel

theorem q_target_degree_and_canonical : ∀ i : Fin 120,
    IsCapped (qTargetExponent i) ∧ weightedDegree (qTargetExponent i) = 16 ∧
      Canonical true (qTargetExponent i) := by decide +kernel

theorem hq_target_degree_and_canonical : ∀ i : Fin 74,
    IsCapped (hqTargetExponent i) ∧ weightedDegree (hqTargetExponent i) = 17 ∧
      Canonical true (hqTargetExponent i) := by decide +kernel

#print axioms orbitCodes_complete

end WeightedSupport.PolynomialModel
