import EnvelopingIsomorphism.Deformation.GraphWeightedInsertion
import EnvelopingIsomorphism.FormalSeries.BinaryAssociator
import EnvelopingIsomorphism.Deformation.Gauge.GraphFirstCoefficient

/-! Finite scalar graph profiles of the full associator coefficient at a fixed
number of binary vertices. Every degree split, weight product and actual graft
assignment is retained, including the zero-vertex graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
namespace EnvelopingIsomorphism.Deformation.GraphAssociatorProfiles
open UniformBinaryGraphs GraphWeightedInsertion GraphCoefficientProfiles
open EnvelopingIsomorphism.FormalSeries
open scoped BigOperators Classical

variable {k : Type*} [CommRing k] {d n N : ℕ}

/-- Equality of vertex counts transports the actual graph structure, with no
permutation or weight-invariance assumption. -/
def castVertices {m : ℕ} (h : n = N) (Γ : BinaryGraph n m) : BinaryGraph N m := h ▸ Γ

/-- The corresponding transport of a scalar coefficient table. -/
def castProfile (h : n = N) (w : BinaryGraph n 3 → k) : BinaryGraph N 3 → k := h ▸ w

omit [CommRing k] in
theorem castProfile_apply (h : n = N) (w : BinaryGraph n 3 → k) (H : BinaryGraph N 3) :
    castProfile h w H = w (castVertices h.symm H) := by
  cases h
  rfl

theorem ternaryValue_castVertices (h : n = N) (π : Bivector (k := k) (d := d))
    (Γ : BinaryGraph n 3) : ternaryValue π (castVertices h Γ) = ternaryValue π Γ := by
  cases h
  rfl

theorem evaluation_castProfile (h : n = N) (w : BinaryGraph n 3 → k)
    (π : Bivector (k := k) (d := d)) :
    evaluation (ternaryValue π) (castProfile h w) = evaluation (ternaryValue π) w := by
  cases h
  rfl

theorem castProfile_graftProfile_apply {a b : ℕ} (h : a+b = N) (r : Fin 2)
    (w : BinaryGraph a 2 → k) (v : BinaryGraph b 2 → k) (H : BinaryGraph N 3) :
    castProfile h (graftProfile r w v) H =
      ∑ Γ : BinaryGraph a 2, ∑ Δ : BinaryGraph b 2, ∑ χ : GraftChoices (b := b) Γ r,
        if castVertices h (uniformGraft Γ Δ r χ) = H then w Γ * v Δ else 0 := by
  cases h
  exact graftProfile_apply r w v H

/-- Every summation index has a proved actual total vertex count N. -/
theorem splitDegree (N : ℕ) (a : Fin (N+1)) : (a : ℕ) + (N - (a : ℕ)) = N :=
  Nat.add_sub_of_le (Nat.le_of_lt_succ a.isLt)

/-- The full scalar associator profile: all degree splittings and left-minus-right grafts. -/
def associatorProfile (N : ℕ) (w : (n : ℕ) → BinaryGraph n 2 → k) : BinaryGraph N 3 → k :=
  ∑ a : Fin (N+1),
    (castProfile (splitDegree N a) (graftProfile 0 (w a) (w (N-a))) -
      castProfile (splitDegree N a) (graftProfile 1 (w a) (w (N-a))))

/-- An explicit finite scalar table, independent of cochains and polynomial test inputs.
Any factorial normalization is already part of the given actual weights. -/
theorem associatorProfile_apply (N : ℕ) (w : (n : ℕ) → BinaryGraph n 2 → k)
    (H : BinaryGraph N 3) :
    associatorProfile N w H = ∑ a : Fin (N+1),
      ((∑ Γ : BinaryGraph (a : ℕ) 2, ∑ Δ : BinaryGraph (N-a) 2,
          ∑ χ : GraftChoices (b := N-a) Γ 0,
            if castVertices (splitDegree N a) (uniformGraft Γ Δ 0 χ) = H
              then w a Γ * w (N-a) Δ else 0) -
        ∑ Γ : BinaryGraph (a : ℕ) 2, ∑ Δ : BinaryGraph (N-a) 2,
          ∑ χ : GraftChoices (b := N-a) Γ 1,
            if castVertices (splitDegree N a) (uniformGraft Γ Δ 1 χ) = H
              then w a Γ * w (N-a) Δ else 0) := by
  simp only [associatorProfile, Finset.sum_apply, Pi.sub_apply, castProfile_graftProfile_apply]

/-- The honest coefficient-cochain series of the weighted binary graph operators. -/
def binarySeries (w : (n : ℕ) → BinaryGraph n 2 → k) (π : Bivector (k := k) (d := d)) :
    PowerSeriesModule k (Binary k (MvPolynomial (Fin d) k)) :=
  PowerSeriesModule.mk (fun n ↦ weightedBinary (w n) π)

@[simp] theorem coeff_binarySeries (w : (n : ℕ) → BinaryGraph n 2 → k)
    (π : Bivector (k := k) (d := d)) (n : ℕ) :
    PowerSeriesModule.coeffV n (binarySeries w π) = weightedBinary (w n) π := rfl

theorem evaluation_associatorProfile_sum (N : ℕ) (w : (n : ℕ) → BinaryGraph n 2 → k)
    (π : Bivector (k := k) (d := d)) :
    evaluation (ternaryValue π) (associatorProfile N w) =
      ∑ a : Fin (N+1), insertBinary (weightedBinary (w a) π) (weightedBinary (w (N-a)) π) := by
  rw [associatorProfile, map_sum]
  simp only [map_sub, evaluation_castProfile, evaluation_graftProfile_left,
    evaluation_graftProfile_right]
  rfl

/-- Evaluating the pure scalar graph table gives the exact coefficient of the
actual quadratic associator convolution. No associativity hypothesis is used. -/
theorem evaluation_associatorProfile (N : ℕ) (w : (n : ℕ) → BinaryGraph n 2 → k)
    (π : Bivector (k := k) (d := d)) :
    evaluation (ternaryValue π) (associatorProfile N w) =
      PowerSeriesModule.coeffV N (PowerSeriesModule.applyBilinear
        (PowerSeriesModule.insertBinaryLinear (k := k) (V := MvPolynomial (Fin d) k))
        (binarySeries w π) (binarySeries w π)) := by
  rw [evaluation_associatorProfile_sum, PowerSeriesModule.coeffV_applyBilinear,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Fin.sum_univ_eq_sum_range]
  rfl

/-- The zero-degree coefficient is included, with the actual empty-graph operation. -/
theorem evaluation_associatorProfile_zero (w : (n : ℕ) → BinaryGraph n 2 → k)
    (π : Bivector (k := k) (d := d)) :
    evaluation (ternaryValue π) (associatorProfile 0 w) =
      insertBinary (weightedBinary (w 0) π) (weightedBinary (w 0) π) := by
  rw [evaluation_associatorProfile_sum]
  simp

/-- At degree one both ordered splits are retained. -/
theorem evaluation_associatorProfile_one (w : (n : ℕ) → BinaryGraph n 2 → k)
    (π : Bivector (k := k) (d := d)) :
    evaluation (ternaryValue π) (associatorProfile 1 w) =
      insertBinary (weightedBinary (w 0) π) (weightedBinary (w 1) π) +
        insertBinary (weightedBinary (w 1) π) (weightedBinary (w 0) π) := by
  rw [evaluation_associatorProfile_sum, Fin.sum_univ_two]
  rfl

theorem weightedBinary_zero (w : BinaryGraph 0 2 → k) (π : Bivector (k := k) (d := d)) :
    weightedBinary w π = w (emptyGraph 2) • LinearMap.mul k (MvPolynomial (Fin d) k) := by
  rw [weightedBinary, Fintype.sum_unique]
  change w (emptyGraph 2) • cochainTwoEquiv k _ (operator (emptyGraph 2) (fun _ ↦ π)) = _
  rw [operator_emptyGraph_two]

private theorem insertBinary_smul_smul (a b : k) (B C : Binary k (MvPolynomial (Fin d) k)) :
    insertBinary (a • B) (b • C) = (a*b) • insertBinary B C := by
  change PowerSeriesModule.insertBinaryLinear (a • B) (b • C) = _
  simp only [map_smul, LinearMap.smul_apply, smul_smul]
  rw [mul_comm b a]
  rfl

/-- The empty-graph term is associative for every scalar weight. -/
theorem evaluation_associatorProfile_zero_eq_zero (w : (n : ℕ) → BinaryGraph n 2 → k)
    (π : Bivector (k := k) (d := d)) :
    evaluation (ternaryValue π) (associatorProfile 0 w) = 0 := by
  rw [evaluation_associatorProfile_zero, weightedBinary_zero, insertBinary_smul_smul]
  have hm : insertBinary (LinearMap.mul k (MvPolynomial (Fin d) k))
      (LinearMap.mul k (MvPolynomial (Fin d) k)) = 0 := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro z
    change (x*y)*z-x*(y*z) = 0
    rw [mul_assoc, sub_self]
  rw [hm, smul_zero]

section OneVertex
variable {K : Type*} [Field K]

/-- The existing two-graph classification, with their actual arbitrary weights. -/
theorem weightedBinary_one (w : BinaryGraph 1 2 → K) (π : Bivector (k := K) (d := d)) :
    weightedBinary w π =
      (w (KontsevichGraph.General.ofBinary Kontsevich.forwardGraph) -
        w (KontsevichGraph.General.ofBinary Kontsevich.reverseGraph)) • rawBivector π := by
  have hsum : weightedBinary w π = ∑ Γ : KontsevichGraph 1,
      w (KontsevichGraph.General.ofBinary Γ) • Gauge.GraphTaylorCoefficients.graphCoefficient Γ (fun _ ↦ π) := by
    unfold weightedBinary
    apply Fintype.sum_equiv (legacyEquiv 1)
    intro Γ
    change w Γ • binaryValue π Γ = w (KontsevichGraph.General.ofBinary (toLegacy Γ)) •
      Gauge.GraphTaylorCoefficients.graphCoefficient (toLegacy Γ) (fun _ ↦ π)
    rw [ofBinary_toLegacy]
    exact congrArg (fun v ↦ w Γ • v) (operator_legacy Γ (fun _ ↦ π))
  rw [hsum, Kontsevich.oneVertex_graph_univ, Finset.sum_pair Kontsevich.forwardGraph_ne_reverseGraph,
    Gauge.GraphFirstCoefficient.graphCoefficient_forward, Gauge.GraphFirstCoefficient.graphCoefficient_reverse,
    smul_neg, ← sub_eq_add_neg, ← sub_smul]

private theorem rawBivector_leibniz_left (π : Bivector (k := K) (d := d))
    (x y z : MvPolynomial (Fin d) K) :
    rawBivector π (x*y) z = x * rawBivector π y z + y * rawBivector π x z := by
  have h := π.leibniz (0 : Fin 2) ![x,z] x y
  have hu (a : MvPolynomial (Fin d) K) : Function.update ![x,z] (0 : Fin 2) a = ![a,z] := by
    funext j
    fin_cases j <;> simp
  rw [hu, hu, hu] at h
  simp only [rawBivector_apply]
  exact h

private theorem rawBivector_leibniz_right (π : Bivector (k := K) (d := d))
    (x y z : MvPolynomial (Fin d) K) :
    rawBivector π x (y*z) = y * rawBivector π x z + z * rawBivector π x y := by
  have h := π.leibniz (1 : Fin 2) ![x,z] y z
  have hu (a : MvPolynomial (Fin d) K) : Function.update ![x,z] (1 : Fin 2) a = ![x,a] := by
    funext j
    fin_cases j <;> simp
  rw [hu, hu, hu] at h
  simp only [rawBivector_apply]
  exact h

/-- A genuine polynomial bivector is a Hochschild cocycle by its two Leibniz rules. -/
theorem insertion_mul_rawBivector (π : Bivector (k := K) (d := d)) :
    insertBinary (LinearMap.mul K (MvPolynomial (Fin d) K)) (rawBivector π) +
      insertBinary (rawBivector π) (LinearMap.mul K (MvPolynomial (Fin d) K)) = 0 := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  apply LinearMap.ext
  intro z
  change (rawBivector π x y * z - x * rawBivector π y z) +
    (rawBivector π (x*y) z - rawBivector π x (y*z)) = 0
  rw [rawBivector_leibniz_left, rawBivector_leibniz_right]
  ring

/-- The degree-one associator coefficient vanishes for arbitrary actual graph
weights; no geometric identity is hidden in this low-degree case. -/
theorem evaluation_associatorProfile_one_eq_zero (w : (n : ℕ) → BinaryGraph n 2 → K)
    (π : Bivector (k := K) (d := d)) :
    evaluation (ternaryValue π) (associatorProfile 1 w) = 0 := by
  rw [evaluation_associatorProfile_one, weightedBinary_zero, weightedBinary_one,
    insertBinary_smul_smul, insertBinary_smul_smul, mul_comm _ (w 0 (emptyGraph 2)),
    ← smul_add, insertion_mul_rawBivector, smul_zero]

end OneVertex
end EnvelopingIsomorphism.Deformation.GraphAssociatorProfiles
