import EnvelopingIsomorphism.Deformation.Kontsevich.ConfigurationTopology
import EnvelopingIsomorphism.Deformation.Kontsevich.PositiveScaleBounds

/-!
# Interior cluster data and a genuine positive-scale configuration

The primitive data are upper-half-plane base points, complex velocities, and
ordered real boundary points. Equal base points must have distinct velocities.
A common positive safe scale exists by finiteness. Explicit norm inequalities
then imply positivity and injectivity of the scaled point coordinates.

`SingleInteriorCluster` imposes the fixed combinatorial pattern of one cluster.
The generic data are deliberately suitable for refinement to forest-node data.
No openness, atlas coverage, or Stokes identity is included in these structures.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration ComplexConjugate
open scoped UpperHalfPlane

/-- First-order collision data normalized at the chosen interior label. -/
structure InteriorCollisionData {n : ℕ} (i : Fin n) (m : ℕ) where
  base : Fin n → ℍ
  velocity : Fin n → ℂ
  separated : ∀ a b, base a = base b → velocity a = velocity b → a = b
  boundary : Fin m → ℝ
  boundary_strictMono : StrictMono boundary
  base_normalized : base i = UpperHalfPlane.I
  velocity_normalized : velocity i = 0

namespace InteriorCollisionData

variable {n m : ℕ} {i : Fin n}

/-- Explicit sufficient inequalities for every scale in `[0, ε]`. -/
structure IsSafeScale (D : InteriorCollisionData i m) (ε : ℝ) : Prop where
  pos : 0 < ε
  height : ∀ a, ε * ‖D.velocity a‖ < (D.base a).im
  separation : ∀ a b, D.base a ≠ D.base b →
    ε * ‖D.velocity a - D.velocity b‖ < ‖(D.base a : ℂ) - (D.base b : ℂ)‖

/-- Every finite set of collision data has an actual positive safe scale. -/
theorem exists_safeScale (D : InteriorCollisionData i m) : ∃ ε, D.IsSafeScale ε := by
  classical
  let P := {p : Fin n × Fin n // D.base p.1 ≠ D.base p.2}
  let a : Fin n ⊕ P → ℝ := Sum.elim (fun j => ‖D.velocity j‖)
    (fun p => ‖D.velocity p.val.1 - D.velocity p.val.2‖)
  let b : Fin n ⊕ P → ℝ := Sum.elim (fun j => (D.base j).im)
    (fun p => ‖(D.base p.val.1 : ℂ) - (D.base p.val.2 : ℂ)‖)
  have ha : ∀ j, 0 ≤ a j := by
    intro j
    cases j <;> exact norm_nonneg _
  have hb : ∀ j, 0 < b j := by
    intro j
    cases j with
    | inl j => exact (D.base j).im_pos
    | inr p =>
      exact norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => p.property (UpperHalfPlane.ext h)))
  obtain ⟨ε, hε, hbound⟩ := exists_uniform_pos_mul_lt a b ha hb
  refine ⟨ε, hε, fun j => hbound (Sum.inl j), fun j k hjk => ?_⟩
  exact hbound (Sum.inr ⟨(j, k), hjk⟩)

theorem scaled_im_pos (D : InteriorCollisionData i m) {ε r : ℝ} (hε : D.IsSafeScale ε)
    (hr : 0 ≤ r) (hrε : r ≤ ε) (a : Fin n) :
    0 < ((D.base a : ℂ) + (r : ℂ) * D.velocity a).im := by
  have hvel := (abs_le.mp (Complex.abs_im_le_norm (D.velocity a))).1
  have hmul := mul_le_mul_of_nonneg_left hvel hr
  have hbound := mul_le_mul_of_nonneg_right hrε (norm_nonneg (D.velocity a))
  have hheight := hε.height a
  simp only [Complex.add_im, UpperHalfPlane.coe_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]
  nlinarith

def scaledPoint (D : InteriorCollisionData i m) {ε r : ℝ} (hε : D.IsSafeScale ε)
    (hr : 0 ≤ r) (hrε : r ≤ ε) (a : Fin n) : ℍ :=
  ⟨(D.base a : ℂ) + (r : ℂ) * D.velocity a, D.scaled_im_pos hε hr hrε a⟩

@[simp] theorem scaledPoint_coe (D : InteriorCollisionData i m) {ε r : ℝ} (hε : D.IsSafeScale ε)
    (hr : 0 ≤ r) (hrε : r ≤ ε) (a : Fin n) :
    (D.scaledPoint hε hr hrε a : ℂ) = (D.base a : ℂ) + (r : ℂ) * D.velocity a := rfl

/-- Positive-scale points are distinct by the primitive velocity and norm conditions. -/
theorem scaledPoint_injective (D : InteriorCollisionData i m) {ε r : ℝ} (hε : D.IsSafeScale ε)
    (hr : 0 < r) (hrε : r ≤ ε) : Function.Injective (D.scaledPoint hε hr.le hrε) := by
  intro a b hab
  have hab' := congrArg (fun z : ℍ => (z : ℂ)) hab
  change (D.base a : ℂ) + (r : ℂ) * D.velocity a =
    (D.base b : ℂ) + (r : ℂ) * D.velocity b at hab'
  by_cases hb : D.base a = D.base b
  · apply D.separated a b hb
    apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne')
    apply add_left_cancel (a := (D.base b : ℂ))
    simpa only [hb] using hab'
  · exfalso
    have hbound : r * ‖D.velocity a - D.velocity b‖ < ‖(D.base a : ℂ) - (D.base b : ℂ)‖ :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hrε (norm_nonneg _)) (hε.separation a b hb)
    exact add_real_mul_ne_of_mul_norm_lt r hr.le (D.base a) (D.base b)
      (D.velocity a) (D.velocity b) hbound hab'

def configuration (D : InteriorCollisionData i m) {ε r : ℝ} (hε : D.IsSafeScale ε)
    (hr : 0 < r) (hrε : r ≤ ε) : Configuration n m where
  interior := D.scaledPoint hε hr.le hrε
  boundary := D.boundary
  interior_injective := D.scaledPoint_injective hε hr hrε
  boundary_strictMono := D.boundary_strictMono

def normalized (D : InteriorCollisionData i m) {ε r : ℝ} (hε : D.IsSafeScale ε)
    (hr : 0 < r) (hrε : r ≤ ε) : Configuration.Normalized i m :=
  ⟨D.configuration hε hr hrε, by
    apply UpperHalfPlane.ext
    simp [configuration, D.base_normalized, D.velocity_normalized]⟩

def doubledBase (D : InteriorCollisionData i m) : DoubledLabel n m → ℂ
  | Sum.inl (Sum.inl a) => D.base a
  | Sum.inl (Sum.inr j) => D.boundary j
  | Sum.inr a => conj (D.base a : ℂ)

def doubledVelocity (D : InteriorCollisionData i m) : DoubledLabel n m → ℂ
  | Sum.inl (Sum.inl a) => D.velocity a
  | Sum.inl (Sum.inr _) => 0
  | Sum.inr a => conj (D.velocity a)

theorem normalized_doubledPoint (D : InteriorCollisionData i m) {ε r : ℝ}
    (hε : D.IsSafeScale ε) (hr : 0 < r) (hrε : r ≤ ε) (v : DoubledLabel n m) :
    (D.normalized hε hr hrε).val.doubledPoint v =
      D.doubledBase v + (r : ℂ) * D.doubledVelocity v := by
  cases v with
  | inl v =>
    cases v with
    | inl a => rfl
    | inr j => simp [normalized, configuration, doubledPoint, vertexPoint, doubledBase, doubledVelocity]
  | inr a =>
    simp [normalized, configuration, doubledPoint, doubledBase, doubledVelocity]

def pairBase (D : InteriorCollisionData i m) (p : DoubledPair n m) : ℂ :=
  D.doubledBase p.val.2 - D.doubledBase p.val.1

def pairVelocity (D : InteriorCollisionData i m) (p : DoubledPair n m) : ℂ :=
  D.doubledVelocity p.val.2 - D.doubledVelocity p.val.1

theorem normalized_pairDifference (D : InteriorCollisionData i m) {ε r : ℝ}
    (hε : D.IsSafeScale ε) (hr : 0 < r) (hrε : r ≤ ε) (p : DoubledPair n m) :
    (D.normalized hε hr hrε).val.pairDifference p = D.pairBase p + (r : ℂ) * D.pairVelocity p := by
  rw [pairDifference, D.normalized_doubledPoint, D.normalized_doubledPoint]
  unfold pairBase pairVelocity
  ring

theorem pairVelocity_ne_zero_of_pairBase_eq_zero (D : InteriorCollisionData i m)
    (p : DoubledPair n m) (hp : D.pairBase p = 0) : D.pairVelocity p ≠ 0 := by
  obtain ⟨ε, hε⟩ := D.exists_safeScale
  let c := D.normalized hε hε.pos (le_refl ε)
  intro hv
  apply c.val.pairDifference_ne_zero p
  rw [D.normalized_pairDifference, hp, hv]
  simp

end InteriorCollisionData

/-- A prescribed nonempty interior cluster, with stationary points outside it.

The singleton case is allowed as data; genuine codimension-one interior
collisions additionally require at least two cluster labels.
-/
structure SingleInteriorCluster {n : ℕ} (i : Fin n) (m : ℕ) (S : Finset (Fin n))
    extends InteriorCollisionData i m where
  cluster_nonempty : S.Nonempty
  base_eq_iff : ∀ a b, base a = base b ↔ a = b ∨ (a ∈ S ∧ b ∈ S)
  velocity_zero_off : ∀ a, a ∉ S → velocity a = 0

namespace SingleInteriorCluster

variable {n m : ℕ} {i : Fin n} {S : Finset (Fin n)}

theorem base_eq_of_mem (D : SingleInteriorCluster i m S) {a b : Fin n} (ha : a ∈ S) (hb : b ∈ S) :
    D.base a = D.base b := (D.base_eq_iff a b).mpr (Or.inr ⟨ha, hb⟩)

theorem velocity_ne_of_mem (D : SingleInteriorCluster i m S) {a b : Fin n}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) : D.velocity a ≠ D.velocity b :=
  fun h => hab (D.separated a b (D.base_eq_of_mem ha hb) h)

end SingleInteriorCluster

end EnvelopingIsomorphism.Deformation.Kontsevich
