import EnvelopingIsomorphism.Deformation.Kontsevich.ConfigurationTopology
import EnvelopingIsomorphism.Deformation.Kontsevich.PositiveScaleBounds

/-!
# Boundary-cluster data and actual configurations at positive scale

A fixed nonempty interior cluster and a consecutive (possibly empty) block of
boundary labels converge to a real center. The remaining points are stationary.
Primitive positivity and separation conditions give a common positive safe
scale and genuine normalized configurations throughout that scale interval.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration ComplexConjugate
open scoped UpperHalfPlane

/-- The half-open consecutive block of boundary labels; it is empty when `l = u`. -/
def boundaryClusterBlock {m : ℕ} (l u : Fin (m + 1)) : Finset (Fin m) :=
  Finset.univ.filter (fun j => l.val ≤ j.val ∧ j.val < u.val)

@[simp] theorem mem_boundaryClusterBlock {m : ℕ} (l u : Fin (m + 1)) (j : Fin m) :
    j ∈ boundaryClusterBlock l u ↔ l.val ≤ j.val ∧ j.val < u.val := by
  simp [boundaryClusterBlock]

@[simp] theorem boundaryClusterBlock_self {m : ℕ} (l : Fin (m + 1)) :
    boundaryClusterBlock l l = ∅ := by
  ext j
  simp only [mem_boundaryClusterBlock, Finset.notMem_empty, iff_false, not_and]
  omega

/-- Primitive coordinates for a real-boundary collision. No positive-scale
injectivity or configuration is assumed. -/
structure BoundaryClusterData {n : ℕ} (i a : Fin n) (m : ℕ) (S : Finset (Fin n))
    (l u : Fin (m + 1)) where
  center : ℝ
  base : Fin n → ℂ
  velocity : Fin n → ℂ
  boundaryBase : Fin m → ℝ
  boundaryVelocity : Fin m → ℝ
  anchor_mem : a ∈ S
  normalized_not_mem : i ∉ S
  block_order : l ≤ u
  base_eq_center : ∀ j, j ∈ S → base j = (center : ℂ)
  base_im_pos_off : ∀ j, j ∉ S → 0 < (base j).im
  base_injective_off : ∀ j k, j ∉ S → k ∉ S → base j = base k → j = k
  base_normalized : base i = Complex.I
  velocity_im_pos : ∀ j, j ∈ S → 0 < (velocity j).im
  velocity_zero_off : ∀ j, j ∉ S → velocity j = 0
  velocity_injective_on : ∀ j k, j ∈ S → k ∈ S → velocity j = velocity k → j = k
  velocity_anchor : velocity a = Complex.I
  boundaryBase_eq_center : ∀ j, j ∈ boundaryClusterBlock l u → boundaryBase j = center
  boundaryBase_lt_center : ∀ j, j.val < l.val → boundaryBase j < center
  center_lt_boundaryBase : ∀ j, u.val ≤ j.val → center < boundaryBase j
  boundaryBase_lt : ∀ j k, j < k →
    ¬(j ∈ boundaryClusterBlock l u ∧ k ∈ boundaryClusterBlock l u) → boundaryBase j < boundaryBase k
  boundaryVelocity_zero_off : ∀ j, j ∉ boundaryClusterBlock l u → boundaryVelocity j = 0
  boundaryVelocity_strictMono_on : ∀ j k, j ∈ boundaryClusterBlock l u →
    k ∈ boundaryClusterBlock l u → j < k → boundaryVelocity j < boundaryVelocity k

namespace BoundaryClusterData

variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

theorem cluster_nonempty (D : BoundaryClusterData i a m S l u) : S.Nonempty :=
  ⟨a, D.anchor_mem⟩

theorem velocity_normalized (D : BoundaryClusterData i a m S l u) : D.velocity i = 0 :=
  D.velocity_zero_off i D.normalized_not_mem

theorem base_ne_of_mem_off (D : BoundaryClusterData i a m S l u) {j k : Fin n}
    (hj : j ∈ S) (hk : k ∉ S) : D.base j ≠ D.base k := by
  intro h
  have hpos := D.base_im_pos_off k hk
  rw [← h, D.base_eq_center j hj, Complex.ofReal_im] at hpos
  exact lt_irrefl _ hpos

theorem base_eq_iff (D : BoundaryClusterData i a m S l u) (j k : Fin n) :
    D.base j = D.base k ↔ j = k ∨ (j ∈ S ∧ k ∈ S) := by
  constructor
  · intro h
    by_cases hj : j ∈ S
    · by_cases hk : k ∈ S
      · exact Or.inr ⟨hj, hk⟩
      · exact False.elim (D.base_ne_of_mem_off hj hk h)
    · by_cases hk : k ∈ S
      · exact False.elim (D.base_ne_of_mem_off hk hj h.symm)
      · exact Or.inl (D.base_injective_off j k hj hk h)
  · rintro (rfl | ⟨hj, hk⟩)
    · rfl
    · rw [D.base_eq_center j hj, D.base_eq_center k hk]

theorem separated (D : BoundaryClusterData i a m S l u) (j k : Fin n)
    (hbase : D.base j = D.base k) (hvel : D.velocity j = D.velocity k) : j = k := by
  rcases (D.base_eq_iff j k).mp hbase with h | ⟨hj, hk⟩
  · exact h
  · exact D.velocity_injective_on j k hj hk hvel

theorem boundaryBase_monotone (D : BoundaryClusterData i a m S l u) : Monotone D.boundaryBase := by
  intro j k hjk
  rcases hjk.eq_or_lt with rfl | hlt
  · exact le_rfl
  · by_cases hblock : j ∈ boundaryClusterBlock l u ∧ k ∈ boundaryClusterBlock l u
    · rw [D.boundaryBase_eq_center j hblock.1, D.boundaryBase_eq_center k hblock.2]
    · exact (D.boundaryBase_lt j k hlt hblock).le

/-- Sufficient finite displacement bounds, without any requested conclusion
about the scaled configuration appearing among the assumptions. -/
structure IsSafeScale (D : BoundaryClusterData i a m S l u) (ε : ℝ) : Prop where
  pos : 0 < ε
  separation : ∀ j k, D.base j ≠ D.base k →
    ε * ‖D.velocity j - D.velocity k‖ < ‖D.base j - D.base k‖
  boundary_separation : ∀ j k, j < k →
    ¬(j ∈ boundaryClusterBlock l u ∧ k ∈ boundaryClusterBlock l u) →
    ε * |D.boundaryVelocity k - D.boundaryVelocity j| < D.boundaryBase k - D.boundaryBase j

theorem exists_safeScale (D : BoundaryClusterData i a m S l u) : ∃ ε, D.IsSafeScale ε := by
  classical
  let P := {p : Fin n × Fin n // D.base p.1 ≠ D.base p.2}
  let Q := {p : Fin m × Fin m // p.1 < p.2 ∧
    ¬(p.1 ∈ boundaryClusterBlock l u ∧ p.2 ∈ boundaryClusterBlock l u)}
  let v : P ⊕ Q → ℝ := Sum.elim
    (fun p => ‖D.velocity p.val.1 - D.velocity p.val.2‖)
    (fun p => |D.boundaryVelocity p.val.2 - D.boundaryVelocity p.val.1|)
  let d : P ⊕ Q → ℝ := Sum.elim
    (fun p => ‖D.base p.val.1 - D.base p.val.2‖)
    (fun p => D.boundaryBase p.val.2 - D.boundaryBase p.val.1)
  have hv : ∀ p, 0 ≤ v p := by
    intro p
    cases p with
    | inl p => exact norm_nonneg _
    | inr p => exact abs_nonneg _
  have hd : ∀ p, 0 < d p := by
    intro p
    cases p with
    | inl p => exact norm_pos_iff.mpr (sub_ne_zero.mpr p.property)
    | inr p => exact sub_pos.mpr (D.boundaryBase_lt _ _ p.property.1 p.property.2)
  obtain ⟨ε, hε, hbound⟩ := exists_uniform_pos_mul_lt v d hv hd
  exact ⟨ε, hε, fun j k hjk => hbound (Sum.inl ⟨(j, k), hjk⟩),
    fun j k hjk hblock => hbound (Sum.inr ⟨(j, k), hjk, hblock⟩)⟩

def scaledInterior (D : BoundaryClusterData i a m S l u) (r : ℝ) (j : Fin n) : ℂ :=
  D.base j + (r : ℂ) * D.velocity j

def scaledBoundary (D : BoundaryClusterData i a m S l u) (r : ℝ) (j : Fin m) : ℝ :=
  D.boundaryBase j + r * D.boundaryVelocity j

/-- Positivity requires only positive scale: inside velocities point upwards,
and the stationary outside base points already lie in the upper half plane. -/
theorem scaledInterior_im_pos (D : BoundaryClusterData i a m S l u) {r : ℝ}
    (hr : 0 < r) (j : Fin n) : 0 < (D.scaledInterior r j).im := by
  by_cases hj : j ∈ S
  · simpa only [scaledInterior, D.base_eq_center j hj, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, zero_mul, add_zero, zero_add] using
      mul_pos hr (D.velocity_im_pos j hj)
  · simpa only [scaledInterior, D.velocity_zero_off j hj, mul_zero, add_zero] using
      D.base_im_pos_off j hj

def scaledPoint (D : BoundaryClusterData i a m S l u) {r : ℝ} (hr : 0 < r) (j : Fin n) : ℍ :=
  ⟨D.scaledInterior r j, D.scaledInterior_im_pos hr j⟩

@[simp] theorem scaledPoint_coe (D : BoundaryClusterData i a m S l u) {r : ℝ}
    (hr : 0 < r) (j : Fin n) : (D.scaledPoint hr j : ℂ) = D.scaledInterior r j := rfl

theorem scaledInterior_injective (D : BoundaryClusterData i a m S l u) {ε r : ℝ}
    (hε : D.IsSafeScale ε) (hr : 0 < r) (hrε : r ≤ ε) :
    Function.Injective (D.scaledInterior r) := by
  intro j k hjk
  change D.base j + (r : ℂ) * D.velocity j = D.base k + (r : ℂ) * D.velocity k at hjk
  by_cases hbase : D.base j = D.base k
  · apply D.separated j k hbase
    apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne')
    apply add_left_cancel (a := D.base k)
    simpa only [hbase] using hjk
  · exfalso
    have hbound : r * ‖D.velocity j - D.velocity k‖ < ‖D.base j - D.base k‖ :=
      (mul_le_mul_of_nonneg_right hrε (norm_nonneg _)).trans_lt (hε.separation j k hbase)
    exact add_real_mul_ne_of_mul_norm_lt r hr.le _ _ _ _ hbound hjk

theorem scaledPoint_injective (D : BoundaryClusterData i a m S l u) {ε r : ℝ}
    (hε : D.IsSafeScale ε) (hr : 0 < r) (hrε : r ≤ ε) :
    Function.Injective (D.scaledPoint hr) := by
  intro j k hjk
  exact D.scaledInterior_injective hε hr hrε (congrArg (fun z : ℍ => (z : ℂ)) hjk)

theorem scaledBoundary_strictMono (D : BoundaryClusterData i a m S l u) {ε r : ℝ}
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

def configuration (D : BoundaryClusterData i a m S l u) {ε r : ℝ} (hε : D.IsSafeScale ε)
    (hr : 0 < r) (hrε : r ≤ ε) : Configuration n m where
  interior := D.scaledPoint hr
  boundary := D.scaledBoundary r
  interior_injective := D.scaledPoint_injective hε hr hrε
  boundary_strictMono := D.scaledBoundary_strictMono hε hr hrε

def normalized (D : BoundaryClusterData i a m S l u) {ε r : ℝ} (hε : D.IsSafeScale ε)
    (hr : 0 < r) (hrε : r ≤ ε) : Configuration.Normalized i m :=
  ⟨D.configuration hε hr hrε, by
    apply UpperHalfPlane.ext
    simp only [configuration, scaledPoint_coe, scaledInterior, D.base_normalized,
      D.velocity_normalized, mul_zero, add_zero]
    rfl⟩

@[simp] theorem normalized_interior (D : BoundaryClusterData i a m S l u) {ε r : ℝ}
    (hε : D.IsSafeScale ε) (hr : 0 < r) (hrε : r ≤ ε) (j : Fin n) :
    ((D.normalized hε hr hrε).val.interior j : ℂ) = D.base j + (r : ℂ) * D.velocity j := rfl

@[simp] theorem normalized_boundary (D : BoundaryClusterData i a m S l u) {ε r : ℝ}
    (hε : D.IsSafeScale ε) (hr : 0 < r) (hrε : r ≤ ε) (j : Fin m) :
    (D.normalized hε hr hrε).val.boundary j = D.boundaryBase j + r * D.boundaryVelocity j := rfl

def doubledBase (D : BoundaryClusterData i a m S l u) : DoubledLabel n m → ℂ
  | Sum.inl (Sum.inl j) => D.base j
  | Sum.inl (Sum.inr j) => D.boundaryBase j
  | Sum.inr j => conj (D.base j)

def doubledVelocity (D : BoundaryClusterData i a m S l u) : DoubledLabel n m → ℂ
  | Sum.inl (Sum.inl j) => D.velocity j
  | Sum.inl (Sum.inr j) => D.boundaryVelocity j
  | Sum.inr j => conj (D.velocity j)

theorem normalized_doubledPoint (D : BoundaryClusterData i a m S l u) {ε r : ℝ}
    (hε : D.IsSafeScale ε) (hr : 0 < r) (hrε : r ≤ ε) (v : DoubledLabel n m) :
    (D.normalized hε hr hrε).val.doubledPoint v =
      D.doubledBase v + (r : ℂ) * D.doubledVelocity v := by
  cases v with
  | inl v =>
    cases v with
    | inl j => rfl
    | inr j =>
      simp [normalized, configuration, doubledPoint, vertexPoint, doubledBase, doubledVelocity,
        scaledBoundary]
  | inr j =>
    simp [normalized, configuration, doubledPoint, doubledBase, doubledVelocity, scaledInterior]

def pairBase (D : BoundaryClusterData i a m S l u) (p : DoubledPair n m) : ℂ :=
  D.doubledBase p.val.2 - D.doubledBase p.val.1

def pairVelocity (D : BoundaryClusterData i a m S l u) (p : DoubledPair n m) : ℂ :=
  D.doubledVelocity p.val.2 - D.doubledVelocity p.val.1

theorem normalized_pairDifference (D : BoundaryClusterData i a m S l u) {ε r : ℝ}
    (hε : D.IsSafeScale ε) (hr : 0 < r) (hrε : r ≤ ε) (p : DoubledPair n m) :
    (D.normalized hε hr hrε).val.pairDifference p = D.pairBase p + (r : ℂ) * D.pairVelocity p := by
  rw [pairDifference, D.normalized_doubledPoint, D.normalized_doubledPoint]
  unfold pairBase pairVelocity
  ring

theorem pairVelocity_ne_zero_of_pairBase_eq_zero (D : BoundaryClusterData i a m S l u)
    (p : DoubledPair n m) (hp : D.pairBase p = 0) : D.pairVelocity p ≠ 0 := by
  obtain ⟨ε, hε⟩ := D.exists_safeScale
  let c := D.normalized hε hε.pos (le_refl ε)
  intro hv
  apply c.val.pairDifference_ne_zero p
  rw [D.normalized_pairDifference, hp, hv]
  simp

end BoundaryClusterData

end EnvelopingIsomorphism.Deformation.Kontsevich
