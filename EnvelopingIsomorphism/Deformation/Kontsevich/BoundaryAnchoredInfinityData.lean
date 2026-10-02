import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterData
import EnvelopingIsomorphism.Deformation.Kontsevich.RealAnchorNormalization

/-!
# Infinity data with every interior label in the cluster

The coarse cluster node is zero, and one genuine outside boundary label is
normalized to minus one or one according to its side. The inner shape has its
chosen interior anchor at `I`. No outside interior or second original boundary
label is required.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration ComplexConjugate
open scoped UpperHalfPlane

namespace BoundaryAnchoredInfinityData

def referenceSign {m : ℕ} (l : Fin (m + 1)) (o : Fin m) : ℝ :=
  if o.val < l.val then -1 else 1

theorem referenceSign_ne_zero {m : ℕ} (l : Fin (m + 1)) (o : Fin m) :
    referenceSign l o ≠ 0 := by unfold referenceSign; split_ifs <;> norm_num

theorem referenceSign_sq {m : ℕ} (l : Fin (m + 1)) (o : Fin m) :
    referenceSign l o ^ 2 = 1 := by unfold referenceSign; split_ifs <;> norm_num

theorem abs_referenceSign {m : ℕ} (l : Fin (m + 1)) (o : Fin m) :
    |referenceSign l o| = 1 := by unfold referenceSign; split_ifs <;> norm_num

end BoundaryAnchoredInfinityData

structure BoundaryAnchoredInfinityData {n : ℕ} (a : Fin n) (m : ℕ)
    (l u : Fin (m + 1)) (o : Fin m) where
  shape : Fin n → ℍ
  boundaryBase : Fin m → ℝ
  boundaryVelocity : Fin m → ℝ
  shape_injective : Function.Injective shape
  shape_anchor : shape a = UpperHalfPlane.I
  block_order : l ≤ u
  outside_not_mem : o ∉ boundaryClusterBlock l u
  boundaryBase_zero_on : ∀ j, j ∈ boundaryClusterBlock l u → boundaryBase j = 0
  boundaryBase_neg_left : ∀ j, j.val < l.val → boundaryBase j < 0
  boundaryBase_pos_right : ∀ j, u.val ≤ j.val → 0 < boundaryBase j
  boundaryBase_lt : ∀ j k, j < k →
    ¬(j ∈ boundaryClusterBlock l u ∧ k ∈ boundaryClusterBlock l u) → boundaryBase j < boundaryBase k
  boundaryVelocity_zero_off : ∀ j, j ∉ boundaryClusterBlock l u → boundaryVelocity j = 0
  boundaryVelocity_strictMono_on : ∀ j k, j ∈ boundaryClusterBlock l u →
    k ∈ boundaryClusterBlock l u → j < k → boundaryVelocity j < boundaryVelocity k
  boundaryBase_anchor : boundaryBase o = BoundaryAnchoredInfinityData.referenceSign l o

def boundaryAnchoredInfinityCollapses {n m : ℕ} (l u : Fin (m + 1)) : DoubledLabel n m → Prop
  | Sum.inl (Sum.inr j) => j ∈ boundaryClusterBlock l u
  | _ => True

instance {n m : ℕ} (l u : Fin (m + 1)) (v : DoubledLabel n m) :
    Decidable (boundaryAnchoredInfinityCollapses l u v) := by
  unfold boundaryAnchoredInfinityCollapses
  split <;> infer_instance

def boundaryAnchoredInfinityPairCollapses {n m : ℕ} (l u : Fin (m + 1))
    (p : DoubledPair n m) : Prop :=
  boundaryAnchoredInfinityCollapses l u p.val.1 ∧ boundaryAnchoredInfinityCollapses l u p.val.2

instance {n m : ℕ} (l u : Fin (m + 1)) (p : DoubledPair n m) :
    Decidable (boundaryAnchoredInfinityPairCollapses l u p) := inferInstanceAs (Decidable (_ ∧ _))

namespace BoundaryAnchoredInfinityData

variable {n m : ℕ} {a : Fin n} {l u : Fin (m + 1)} {o : Fin m}

theorem boundaryBase_eq_zero_iff (D : BoundaryAnchoredInfinityData a m l u o) (j : Fin m) :
    D.boundaryBase j = 0 ↔ j ∈ boundaryClusterBlock l u := by
  constructor
  · intro h
    by_contra hj
    have hj' : ¬ (l.val ≤ j.val ∧ j.val < u.val) := by
      simpa only [mem_boundaryClusterBlock] using hj
    by_cases hleft : j.val < l.val
    · exact (D.boundaryBase_neg_left j hleft).ne h
    · have hright : u.val ≤ j.val := by omega
      exact (D.boundaryBase_pos_right j hright).ne' h
  · exact D.boundaryBase_zero_on j

theorem boundaryBase_eq_iff (D : BoundaryAnchoredInfinityData a m l u o) (j k : Fin m) :
    D.boundaryBase j = D.boundaryBase k ↔
      j = k ∨ (j ∈ boundaryClusterBlock l u ∧ k ∈ boundaryClusterBlock l u) := by
  constructor
  · intro h
    by_cases hjk : j = k
    · exact Or.inl hjk
    · right
      by_contra hblock
      rcases lt_or_gt_of_ne hjk with hjk | hkj
      · exact (D.boundaryBase_lt j k hjk hblock).ne h
      · exact (D.boundaryBase_lt k j hkj (fun h => hblock h.symm)).ne h.symm
  · rintro (rfl | ⟨hj, hk⟩)
    · rfl
    · rw [D.boundaryBase_zero_on j hj, D.boundaryBase_zero_on k hk]

theorem boundaryBase_outside_ne_zero (D : BoundaryAnchoredInfinityData a m l u o) :
    D.boundaryBase o ≠ 0 := fun h => D.outside_not_mem ((D.boundaryBase_eq_zero_iff o).mp h)

structure IsSafeScale (D : BoundaryAnchoredInfinityData a m l u o) (ε : ℝ) : Prop where
  pos : 0 < ε
  boundary_separation : ∀ j k, j < k →
    ¬(j ∈ boundaryClusterBlock l u ∧ k ∈ boundaryClusterBlock l u) →
    ε * |D.boundaryVelocity k - D.boundaryVelocity j| < D.boundaryBase k - D.boundaryBase j

structure AdmissibleScale (D : BoundaryAnchoredInfinityData a m l u o) (r : ℝ) : Prop where
  nonneg : 0 ≤ r
  boundary_separation : ∀ j k, j < k →
    ¬(j ∈ boundaryClusterBlock l u ∧ k ∈ boundaryClusterBlock l u) →
    r * |D.boundaryVelocity k - D.boundaryVelocity j| < D.boundaryBase k - D.boundaryBase j

theorem admissibleScale_zero (D : BoundaryAnchoredInfinityData a m l u o) : D.AdmissibleScale 0 := by
  refine ⟨le_refl 0, fun j k hjk hblock => ?_⟩
  simpa using sub_pos.mpr (D.boundaryBase_lt j k hjk hblock)

theorem IsSafeScale.admissibleScale {D : BoundaryAnchoredInfinityData a m l u o} {ε r : ℝ}
    (h : D.IsSafeScale ε) (hr : 0 ≤ r) (hrε : r ≤ ε) : D.AdmissibleScale r := by
  refine ⟨hr, fun j k hjk hblock => ?_⟩
  exact (mul_le_mul_of_nonneg_right hrε (abs_nonneg _)).trans_lt
    (h.boundary_separation j k hjk hblock)

theorem AdmissibleScale.isSafeScale {D : BoundaryAnchoredInfinityData a m l u o} {r : ℝ}
    (h : D.AdmissibleScale r) (hr : 0 < r) : D.IsSafeScale r := ⟨hr, h.boundary_separation⟩

theorem exists_safeScale (D : BoundaryAnchoredInfinityData a m l u o) : ∃ ε, D.IsSafeScale ε := by
  classical
  let P := {p : Fin m × Fin m // p.1 < p.2 ∧
    ¬(p.1 ∈ boundaryClusterBlock l u ∧ p.2 ∈ boundaryClusterBlock l u)}
  obtain ⟨ε, hε, hbound⟩ := exists_uniform_pos_mul_lt
    (fun p : P => |D.boundaryVelocity p.val.2 - D.boundaryVelocity p.val.1|)
    (fun p : P => D.boundaryBase p.val.2 - D.boundaryBase p.val.1)
    (fun _ => abs_nonneg _)
    (fun p => sub_pos.mpr (D.boundaryBase_lt _ _ p.property.1 p.property.2))
  exact ⟨ε, hε, fun j k hjk hblock => hbound ⟨(j, k), hjk, hblock⟩⟩

def scaledInterior (D : BoundaryAnchoredInfinityData a m l u o) (r : ℝ) (j : Fin n) : ℂ :=
  (r : ℂ) * (D.shape j : ℂ)

def scaledBoundary (D : BoundaryAnchoredInfinityData a m l u o) (r : ℝ) (j : Fin m) : ℝ :=
  D.boundaryBase j + r * D.boundaryVelocity j

theorem scaledInterior_im_pos (D : BoundaryAnchoredInfinityData a m l u o) {r : ℝ}
    (hr : 0 < r) (j : Fin n) : 0 < (D.scaledInterior r j).im := by
  simpa [scaledInterior] using mul_pos hr (D.shape j).im_pos

def scaledPoint (D : BoundaryAnchoredInfinityData a m l u o) {r : ℝ}
    (hr : 0 < r) (j : Fin n) : ℍ := ⟨D.scaledInterior r j, D.scaledInterior_im_pos hr j⟩

@[simp] theorem scaledPoint_coe (D : BoundaryAnchoredInfinityData a m l u o) {r : ℝ}
    (hr : 0 < r) (j : Fin n) : (D.scaledPoint hr j : ℂ) = D.scaledInterior r j := rfl

theorem scaledPoint_injective (D : BoundaryAnchoredInfinityData a m l u o) {r : ℝ}
    (hr : 0 < r) : Function.Injective (D.scaledPoint hr) := by
  intro j k h
  apply D.shape_injective
  apply UpperHalfPlane.ext
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne')
    (congrArg (fun z : ℍ => (z : ℂ)) h)

theorem scaledBoundary_strictMono (D : BoundaryAnchoredInfinityData a m l u o) {ε r : ℝ}
    (hε : D.IsSafeScale ε) (hr : 0 < r) (hrε : r ≤ ε) : StrictMono (D.scaledBoundary r) := by
  intro j k hjk
  by_cases hblock : j ∈ boundaryClusterBlock l u ∧ k ∈ boundaryClusterBlock l u
  · simp only [scaledBoundary, D.boundaryBase_zero_on j hblock.1,
      D.boundaryBase_zero_on k hblock.2, zero_add]
    exact mul_lt_mul_of_pos_left (D.boundaryVelocity_strictMono_on j k hblock.1 hblock.2 hjk) hr
  · have hbound := (mul_le_mul_of_nonneg_right hrε
      (abs_nonneg (D.boundaryVelocity k - D.boundaryVelocity j))).trans_lt
        (hε.boundary_separation j k hjk hblock)
    have hneg := mul_le_mul_of_nonneg_left
      (neg_abs_le (D.boundaryVelocity k - D.boundaryVelocity j)) hr.le
    dsimp only [scaledBoundary]
    nlinarith

def configuration (D : BoundaryAnchoredInfinityData a m l u o) {ε r : ℝ}
    (hε : D.IsSafeScale ε) (hr : 0 < r) (hrε : r ≤ ε) : Configuration n m where
  interior := D.scaledPoint hr
  boundary := D.scaledBoundary r
  interior_injective := D.scaledPoint_injective hr
  boundary_strictMono := D.scaledBoundary_strictMono hε hr hrε

def normalized (D : BoundaryAnchoredInfinityData a m l u o) {ε r : ℝ}
    (hε : D.IsSafeScale ε) (hr : 0 < r) (hrε : r ≤ ε) : Configuration.Normalized a m :=
  Configuration.normalized a (D.configuration hε hr hrε)

def doubledBase (D : BoundaryAnchoredInfinityData a m l u o) : DoubledLabel n m → ℂ
  | Sum.inl (Sum.inr j) => D.boundaryBase j
  | _ => 0

def doubledVelocity (D : BoundaryAnchoredInfinityData a m l u o) : DoubledLabel n m → ℂ
  | Sum.inl (Sum.inl j) => D.shape j
  | Sum.inl (Sum.inr j) => D.boundaryVelocity j
  | Sum.inr j => conj (D.shape j : ℂ)

theorem configuration_doubledPoint (D : BoundaryAnchoredInfinityData a m l u o) {ε r : ℝ}
    (hε : D.IsSafeScale ε) (hr : 0 < r) (hrε : r ≤ ε) (v : DoubledLabel n m) :
    (D.configuration hε hr hrε).doubledPoint v =
      D.doubledBase v + (r : ℂ) * D.doubledVelocity v := by
  rcases v with (j | j) | j <;>
    simp [configuration, doubledPoint, vertexPoint, doubledBase, doubledVelocity,
      scaledBoundary, scaledInterior]

def pairBase (D : BoundaryAnchoredInfinityData a m l u o) (p : DoubledPair n m) : ℂ :=
  D.doubledBase p.val.2 - D.doubledBase p.val.1

def pairVelocity (D : BoundaryAnchoredInfinityData a m l u o) (p : DoubledPair n m) : ℂ :=
  D.doubledVelocity p.val.2 - D.doubledVelocity p.val.1

theorem configuration_pairDifference (D : BoundaryAnchoredInfinityData a m l u o) {ε r : ℝ}
    (hε : D.IsSafeScale ε) (hr : 0 < r) (hrε : r ≤ ε) (p : DoubledPair n m) :
    (D.configuration hε hr hrε).pairDifference p = D.pairBase p + (r : ℂ) * D.pairVelocity p := by
  rw [pairDifference, D.configuration_doubledPoint, D.configuration_doubledPoint]
  unfold pairBase pairVelocity
  ring

theorem doubledBase_eq_iff (D : BoundaryAnchoredInfinityData a m l u o) (v w : DoubledLabel n m) :
    D.doubledBase v = D.doubledBase w ↔
      v = w ∨ (boundaryAnchoredInfinityCollapses l u v ∧ boundaryAnchoredInfinityCollapses l u w) := by
  rcases v with (v | v) | v <;> rcases w with (w | w) | w <;>
    simp only [doubledBase, boundaryAnchoredInfinityCollapses, true_and, and_true,
      or_true, eq_self, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, false_or]
  · rw [eq_comm, Complex.ofReal_eq_zero, D.boundaryBase_eq_zero_iff]
  · rw [Complex.ofReal_eq_zero, D.boundaryBase_eq_zero_iff]
  · exact Complex.ofReal_injective.eq_iff.trans (D.boundaryBase_eq_iff v w)
  · rw [Complex.ofReal_eq_zero, D.boundaryBase_eq_zero_iff]
  · rw [eq_comm, Complex.ofReal_eq_zero, D.boundaryBase_eq_zero_iff]

theorem pairBase_eq_zero_iff_pairCollapses (D : BoundaryAnchoredInfinityData a m l u o)
    (p : DoubledPair n m) : D.pairBase p = 0 ↔ boundaryAnchoredInfinityPairCollapses l u p := by
  rw [pairBase, sub_eq_zero, D.doubledBase_eq_iff]
  simp only [Ne.symm p.property, false_or, boundaryAnchoredInfinityPairCollapses, and_comm]

theorem pairVelocity_ne_zero_of_pairBase_eq_zero (D : BoundaryAnchoredInfinityData a m l u o)
    (p : DoubledPair n m) (hp : D.pairBase p = 0) : D.pairVelocity p ≠ 0 := by
  obtain ⟨ε, hε⟩ := D.exists_safeScale
  intro hv
  apply (D.configuration hε hε.pos (le_refl ε)).pairDifference_ne_zero p
  rw [D.configuration_pairDifference, hp, hv]
  simp

end BoundaryAnchoredInfinityData

end EnvelopingIsomorphism.Deformation.Kontsevich
