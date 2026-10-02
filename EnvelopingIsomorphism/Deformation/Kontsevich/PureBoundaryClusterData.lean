import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterData

/-!
# Pure boundary clusters and actual positive-scale configurations

Only a consecutive block of at least two external labels collapses. All
interior points are stationary. The endpoint shape coordinates are 0 and 1,
so the left endpoint is the center and the endpoint gap is the radius.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration ComplexConjugate
open scoped UpperHalfPlane

structure PureBoundaryClusterData {n : ℕ} (i : Fin n) (m : ℕ) (l u : Fin (m + 1))
    (a b : Fin m) where
  center : ℝ
  interior : Fin n → ℍ
  boundaryBase : Fin m → ℝ
  boundaryVelocity : Fin m → ℝ
  left_endpoint : a.val = l.val
  right_endpoint : b.val + 1 = u.val
  endpoint_lt : a < b
  interior_injective : Function.Injective interior
  interior_normalized : interior i = UpperHalfPlane.I
  boundaryBase_eq_center : ∀ j, j ∈ boundaryClusterBlock l u → boundaryBase j = center
  boundaryBase_lt_center : ∀ j, j.val < l.val → boundaryBase j < center
  center_lt_boundaryBase : ∀ j, u.val ≤ j.val → center < boundaryBase j
  boundaryBase_lt : ∀ j k, j < k →
    ¬(j ∈ boundaryClusterBlock l u ∧ k ∈ boundaryClusterBlock l u) → boundaryBase j < boundaryBase k
  boundaryVelocity_zero_off : ∀ j, j ∉ boundaryClusterBlock l u → boundaryVelocity j = 0
  boundaryVelocity_strictMono_on : ∀ j k, j ∈ boundaryClusterBlock l u →
    k ∈ boundaryClusterBlock l u → j < k → boundaryVelocity j < boundaryVelocity k
  boundaryVelocity_left : boundaryVelocity a = 0
  boundaryVelocity_right : boundaryVelocity b = 1

def pureBoundaryClusterCollapses {n m : ℕ} (l u : Fin (m + 1)) : DoubledLabel n m → Prop
  | Sum.inl (Sum.inr j) => j ∈ boundaryClusterBlock l u
  | _ => False

instance {n m : ℕ} (l u : Fin (m + 1)) (v : DoubledLabel n m) :
    Decidable (pureBoundaryClusterCollapses l u v) := by
  unfold pureBoundaryClusterCollapses
  split <;> infer_instance

def pureBoundaryClusterPairCollapses {n m : ℕ} (l u : Fin (m + 1)) (p : DoubledPair n m) : Prop :=
  pureBoundaryClusterCollapses l u p.val.1 ∧ pureBoundaryClusterCollapses l u p.val.2

instance {n m : ℕ} (l u : Fin (m + 1)) (p : DoubledPair n m) :
    Decidable (pureBoundaryClusterPairCollapses l u p) := inferInstanceAs (Decidable (_ ∧ _))

namespace PureBoundaryClusterData

variable {n m : ℕ} {i : Fin n} {l u : Fin (m + 1)} {a b : Fin m}

theorem left_mem (D : PureBoundaryClusterData i m l u a b) : a ∈ boundaryClusterBlock l u := by
  rw [mem_boundaryClusterBlock]
  have ha := D.left_endpoint
  have hb := D.right_endpoint
  have hab := D.endpoint_lt
  constructor <;> omega

theorem right_mem (D : PureBoundaryClusterData i m l u a b) : b ∈ boundaryClusterBlock l u := by
  rw [mem_boundaryClusterBlock]
  have ha := D.left_endpoint
  have hb := D.right_endpoint
  have hab := D.endpoint_lt
  constructor <;> omega

theorem block_card_ge_two (D : PureBoundaryClusterData i m l u a b) :
    2 ≤ (boundaryClusterBlock l u).card :=
  Finset.one_lt_card.mpr ⟨a, D.left_mem, b, D.right_mem, D.endpoint_lt.ne⟩

theorem boundaryBase_eq_center_iff (D : PureBoundaryClusterData i m l u a b) (j : Fin m) :
    D.boundaryBase j = D.center ↔ j ∈ boundaryClusterBlock l u := by
  constructor
  · intro h
    by_contra hj
    have hj' : ¬(l.val ≤ j.val ∧ j.val < u.val) := by
      simpa only [mem_boundaryClusterBlock] using hj
    by_cases hleft : j.val < l.val
    · exact (D.boundaryBase_lt_center j hleft).ne h
    · have hright : u.val ≤ j.val := by omega
      exact (D.center_lt_boundaryBase j hright).ne' h
  · exact D.boundaryBase_eq_center j

theorem boundaryBase_eq_iff (D : PureBoundaryClusterData i m l u a b) (j k : Fin m) :
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
      · exact (D.boundaryBase_lt k j hkj (fun hk => hblock hk.symm)).ne h.symm
  · rintro (rfl | ⟨hj, hk⟩)
    · rfl
    · rw [D.boundaryBase_eq_center j hj, D.boundaryBase_eq_center k hk]

structure IsSafeScale (D : PureBoundaryClusterData i m l u a b) (ε : ℝ) : Prop where
  pos : 0 < ε
  boundary_separation : ∀ j k, j < k →
    ¬(j ∈ boundaryClusterBlock l u ∧ k ∈ boundaryClusterBlock l u) →
    ε * |D.boundaryVelocity k - D.boundaryVelocity j| < D.boundaryBase k - D.boundaryBase j

theorem exists_safeScale (D : PureBoundaryClusterData i m l u a b) : ∃ ε, D.IsSafeScale ε := by
  classical
  let P := {p : Fin m × Fin m // p.1 < p.2 ∧
    ¬(p.1 ∈ boundaryClusterBlock l u ∧ p.2 ∈ boundaryClusterBlock l u)}
  obtain ⟨ε, hε, hbound⟩ := exists_uniform_pos_mul_lt
    (fun p : P => |D.boundaryVelocity p.val.2 - D.boundaryVelocity p.val.1|)
    (fun p : P => D.boundaryBase p.val.2 - D.boundaryBase p.val.1)
    (fun _ => abs_nonneg _)
    (fun p => sub_pos.mpr (D.boundaryBase_lt _ _ p.property.1 p.property.2))
  exact ⟨ε, hε, fun j k hjk hblock => hbound ⟨(j, k), hjk, hblock⟩⟩

def scaledBoundary (D : PureBoundaryClusterData i m l u a b) (r : ℝ) (j : Fin m) : ℝ :=
  D.boundaryBase j + r * D.boundaryVelocity j

@[simp] theorem scaledBoundary_left (D : PureBoundaryClusterData i m l u a b) (r : ℝ) :
    D.scaledBoundary r a = D.center := by
  simp only [scaledBoundary, D.boundaryBase_eq_center a D.left_mem,
    D.boundaryVelocity_left, mul_zero, add_zero]

@[simp] theorem scaledBoundary_right (D : PureBoundaryClusterData i m l u a b) (r : ℝ) :
    D.scaledBoundary r b = D.center + r := by
  simp only [scaledBoundary, D.boundaryBase_eq_center b D.right_mem,
    D.boundaryVelocity_right, mul_one]

theorem scaledBoundary_endpoint_gap (D : PureBoundaryClusterData i m l u a b) (r : ℝ) :
    D.scaledBoundary r b - D.scaledBoundary r a = r := by
  rw [D.scaledBoundary_right, D.scaledBoundary_left]
  exact add_sub_cancel_left _ _

theorem scaledBoundary_strictMono (D : PureBoundaryClusterData i m l u a b) {ε r : ℝ}
    (hε : D.IsSafeScale ε) (hr : 0 < r) (hrε : r ≤ ε) : StrictMono (D.scaledBoundary r) := by
  intro j k hjk
  by_cases hblock : j ∈ boundaryClusterBlock l u ∧ k ∈ boundaryClusterBlock l u
  · simp only [scaledBoundary, D.boundaryBase_eq_center j hblock.1,
      D.boundaryBase_eq_center k hblock.2, add_lt_add_iff_left]
    exact mul_lt_mul_of_pos_left (D.boundaryVelocity_strictMono_on j k hblock.1 hblock.2 hjk) hr
  · have hbound := (mul_le_mul_of_nonneg_right hrε
      (abs_nonneg (D.boundaryVelocity k - D.boundaryVelocity j))).trans_lt
        (hε.boundary_separation j k hjk hblock)
    have hneg := mul_le_mul_of_nonneg_left (neg_abs_le (D.boundaryVelocity k - D.boundaryVelocity j)) hr.le
    dsimp only [scaledBoundary]
    nlinarith

def configuration (D : PureBoundaryClusterData i m l u a b) {ε r : ℝ} (hε : D.IsSafeScale ε)
    (hr : 0 < r) (hrε : r ≤ ε) : Configuration n m where
  interior := D.interior
  boundary := D.scaledBoundary r
  interior_injective := D.interior_injective
  boundary_strictMono := D.scaledBoundary_strictMono hε hr hrε

def normalized (D : PureBoundaryClusterData i m l u a b) {ε r : ℝ} (hε : D.IsSafeScale ε)
    (hr : 0 < r) (hrε : r ≤ ε) : Configuration.Normalized i m :=
  ⟨D.configuration hε hr hrε, D.interior_normalized⟩

@[simp] theorem normalized_interior (D : PureBoundaryClusterData i m l u a b) {ε r : ℝ}
    (hε : D.IsSafeScale ε) (hr : 0 < r) (hrε : r ≤ ε) (j : Fin n) :
    (D.normalized hε hr hrε).val.interior j = D.interior j := rfl

@[simp] theorem normalized_boundary (D : PureBoundaryClusterData i m l u a b) {ε r : ℝ}
    (hε : D.IsSafeScale ε) (hr : 0 < r) (hrε : r ≤ ε) (j : Fin m) :
    (D.normalized hε hr hrε).val.boundary j = D.boundaryBase j + r * D.boundaryVelocity j := rfl

def doubledBase (D : PureBoundaryClusterData i m l u a b) : DoubledLabel n m → ℂ
  | Sum.inl (Sum.inl j) => D.interior j
  | Sum.inl (Sum.inr j) => D.boundaryBase j
  | Sum.inr j => conj (D.interior j : ℂ)

def doubledVelocity (D : PureBoundaryClusterData i m l u a b) : DoubledLabel n m → ℂ
  | Sum.inl (Sum.inr j) => D.boundaryVelocity j
  | _ => 0

theorem normalized_doubledPoint (D : PureBoundaryClusterData i m l u a b) {ε r : ℝ}
    (hε : D.IsSafeScale ε) (hr : 0 < r) (hrε : r ≤ ε) (v : DoubledLabel n m) :
    (D.normalized hε hr hrε).val.doubledPoint v =
      D.doubledBase v + (r : ℂ) * D.doubledVelocity v := by
  rcases v with (j | j) | j <;>
    simp [normalized, configuration, doubledPoint, vertexPoint, doubledBase, doubledVelocity, scaledBoundary]

def pairBase (D : PureBoundaryClusterData i m l u a b) (p : DoubledPair n m) : ℂ :=
  D.doubledBase p.val.2 - D.doubledBase p.val.1

def pairVelocity (D : PureBoundaryClusterData i m l u a b) (p : DoubledPair n m) : ℂ :=
  D.doubledVelocity p.val.2 - D.doubledVelocity p.val.1

theorem normalized_pairDifference (D : PureBoundaryClusterData i m l u a b) {ε r : ℝ}
    (hε : D.IsSafeScale ε) (hr : 0 < r) (hrε : r ≤ ε) (p : DoubledPair n m) :
    (D.normalized hε hr hrε).val.pairDifference p = D.pairBase p + (r : ℂ) * D.pairVelocity p := by
  rw [pairDifference, D.normalized_doubledPoint, D.normalized_doubledPoint]
  unfold pairBase pairVelocity
  ring

theorem doubledBase_eq_iff (D : PureBoundaryClusterData i m l u a b) (v w : DoubledLabel n m) :
    D.doubledBase v = D.doubledBase w ↔
      v = w ∨ (pureBoundaryClusterCollapses l u v ∧ pureBoundaryClusterCollapses l u w) := by
  rcases v with (v | v) | v <;> rcases w with (w | w) | w <;>
    simp only [doubledBase, pureBoundaryClusterCollapses, false_and, and_false, or_false,
      Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl]
  · exact ⟨fun h => D.interior_injective (UpperHalfPlane.ext h), fun h => h ▸ rfl⟩
  · apply iff_false_intro
    intro h
    have hi := congrArg Complex.im h
    simp only [UpperHalfPlane.coe_im, Complex.ofReal_im] at hi
    exact (D.interior v).im_pos.ne' hi
  · apply iff_false_intro
    intro h
    have hi := congrArg Complex.im h
    simp only [UpperHalfPlane.coe_im, Complex.conj_im] at hi
    have hv := (D.interior v).im_pos
    have hw := (D.interior w).im_pos
    linarith
  · apply iff_false_intro
    intro h
    have hi := congrArg Complex.im h
    simp only [UpperHalfPlane.coe_im, Complex.ofReal_im] at hi
    exact (D.interior w).im_pos.ne' hi.symm
  · exact Complex.ofReal_injective.eq_iff.trans (D.boundaryBase_eq_iff v w)
  · apply iff_false_intro
    intro h
    have hi := congrArg Complex.im h
    simp only [UpperHalfPlane.coe_im, Complex.ofReal_im, Complex.conj_im] at hi
    have hw := (D.interior w).im_pos
    linarith
  · apply iff_false_intro
    intro h
    have hi := congrArg Complex.im h
    simp only [UpperHalfPlane.coe_im, Complex.conj_im] at hi
    have hv := (D.interior v).im_pos
    have hw := (D.interior w).im_pos
    linarith
  · apply iff_false_intro
    intro h
    have hi := congrArg Complex.im h
    simp only [UpperHalfPlane.coe_im, Complex.ofReal_im, Complex.conj_im] at hi
    have hv := (D.interior v).im_pos
    linarith
  · exact (starRingEnd ℂ).injective.eq_iff.trans
      ⟨fun h => D.interior_injective (UpperHalfPlane.ext h), fun h => h ▸ rfl⟩

theorem pairBase_eq_zero_iff_pureBoundaryClusterPairCollapses (D : PureBoundaryClusterData i m l u a b)
    (p : DoubledPair n m) : D.pairBase p = 0 ↔ pureBoundaryClusterPairCollapses l u p := by
  rw [pairBase, sub_eq_zero, D.doubledBase_eq_iff]
  simp only [Ne.symm p.property, false_or, pureBoundaryClusterPairCollapses, and_comm]

theorem pairVelocity_ne_zero_of_pairBase_eq_zero (D : PureBoundaryClusterData i m l u a b)
    (p : DoubledPair n m) (hp : D.pairBase p = 0) : D.pairVelocity p ≠ 0 := by
  obtain ⟨ε, hε⟩ := D.exists_safeScale
  let c := D.normalized hε hε.pos (le_refl ε)
  intro hv
  apply c.val.pairDifference_ne_zero p
  rw [D.normalized_pairDifference, hp, hv]
  simp

theorem pairVelocity_ne_zero_of_pureBoundaryClusterPairCollapses (D : PureBoundaryClusterData i m l u a b)
    (p : DoubledPair n m) (hp : pureBoundaryClusterPairCollapses l u p) : D.pairVelocity p ≠ 0 :=
  D.pairVelocity_ne_zero_of_pairBase_eq_zero p
    ((D.pairBase_eq_zero_iff_pureBoundaryClusterPairCollapses p).mpr hp)

end PureBoundaryClusterData

end EnvelopingIsomorphism.Deformation.Kontsevich
