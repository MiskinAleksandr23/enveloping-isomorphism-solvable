import EnvelopingIsomorphism.Deformation.Kontsevich.ForestShapeSmooth
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestOrthantCharts
import EnvelopingIsomorphism.Deformation.Kontsevich.LocalAnglePotential

/-! Explicit smooth ambient projections for the actual free forest-shape
coordinates, including the local inverse angle branch. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestShapeProjectionSmooth

open ForestShapeCoordinates ForestFiniteCoordinateProducts ForestNodeShapeCoordinates
open ForestChildShapeDecomposition ForestMarkedFrames ForestParameterProduct
open scoped Classical ContDiff

variable (T : RootedTree) [Fintype T]

/-- The real and imaginary selectors used by a reflected free array. -/
def reflectedRaw (A : Type*) [Fintype A] (σ : A → A) (lab : A → T)
    (q : T → ℂ) : ReflectedRealIndex A σ → ℝ
  | Sum.inl (u, b) => if b then (q (lab u.val)).im else (q (lab u.val)).re
  | Sum.inr u => (q (lab u.val)).re

theorem contDiff_eval_re (v : T) {ν : ℕ∞ω} : ContDiff ℝ ν (fun q : T → ℂ => (q v).re) :=
  Complex.reCLM.contDiff.comp (contDiff_apply ℝ ℂ v)

theorem contDiff_eval_im (v : T) {ν : ℕ∞ω} : ContDiff ℝ ν (fun q : T → ℂ => (q v).im) :=
  Complex.imCLM.contDiff.comp (contDiff_apply ℝ ℂ v)

theorem contDiff_reflectedRaw (A : Type*) [Fintype A] (σ : A → A) (lab : A → T) {ν : ℕ∞ω} :
    ContDiff ℝ ν (reflectedRaw T A σ lab) := by
  apply contDiff_pi.mpr
  intro j
  cases j with
  | inl p =>
    rcases p with ⟨u, b⟩
    cases b
    · simpa [reflectedRaw] using contDiff_eval_re T (lab u.val) (ν := ν)
    · simpa [reflectedRaw] using contDiff_eval_im T (lab u.val) (ν := ν)
  | inr u => exact contDiff_eval_re T (lab u.val)

variable (σ : T ≃o T) (hσ : Function.Involutive σ) (F : Frames T)

def stableRaw (v : FixedParent T σ) (M : StableMarks T σ F v) :
    (T → ℂ) → StableRealIndex T σ hσ F v M → ℝ := by
  letI : DecidableEq (Child T v.val.val) := Classical.decEq _
  cases M with
  | height a ha hf =>
    exact reflectedRaw T (HeightFree (Child T v.val.val) (childReflection T σ v) a)
      (heightReflection _ _ (childReflection_involutive T σ hσ v) a) (fun u => u.val.val)
  | realPair a b hne ha hb hf =>
    exact reflectedRaw T (RealPairFree (Child T v.val.val) a b)
      (realPairReflection _ _ (childReflection_involutive T σ hσ v) a b ha hb) (fun u => u.val.val)

theorem contDiff_stableRaw (v : FixedParent T σ) (M : StableMarks T σ F v) {ν : ℕ∞ω} :
    ContDiff ℝ ν (stableRaw T σ hσ F v M) := by
  apply contDiff_pi.mpr
  intro j
  cases M with
  | height a ha hf =>
    cases j with
    | inl p =>
      rcases p with ⟨u, b⟩
      cases b
      · exact contDiff_eval_re T u.val.val.val
      · exact contDiff_eval_im T u.val.val.val
    | inr u => exact contDiff_eval_re T u.val.val.val
  | realPair a b hne ha hb hf =>
    cases j with
    | inl p =>
      rcases p with ⟨u, b⟩
      cases b
      · exact contDiff_eval_re T u.val.val.val
      · exact contDiff_eval_im T u.val.val.val
    | inr u => exact contDiff_eval_re T u.val.val.val

variable (P : ∀ v : PairParent T σ, ComplexMarks T σ F v.val)
  (S : ∀ v : FixedParent T σ, StableMarks T σ F v)

def circleRaw (q : T → ℂ) (v : PairParent T σ) : ℂ := q (P v).b.val

def realRaw (q : T → ℂ) : RealIndex T σ hσ F P S → ℝ
  | Sum.inl ⟨v, u, b⟩ => if b then (q u.val.val).im else (q u.val.val).re
  | Sum.inr ⟨v, u⟩ => stableRaw T σ hσ F v (S v) q u

theorem contDiff_circleRaw {ν : ℕ∞ω} : ContDiff ℝ ν (circleRaw T σ F P) := by
  apply contDiff_pi.mpr
  intro v
  unfold circleRaw
  fun_prop

theorem contDiff_realRaw {ν : ℕ∞ω} : ContDiff ℝ ν (realRaw T σ hσ F P S) := by
  apply contDiff_pi.mpr
  intro j
  cases j with
  | inl p =>
    rcases p with ⟨v, u, b⟩
    cases b
    · simpa [realRaw] using contDiff_eval_re T u.val.val (ν := ν)
    · simpa [realRaw] using contDiff_eval_im T u.val.val (ν := ν)
  | inr p => exact contDiff_pi.mp (contDiff_stableRaw T σ hσ F p.1 (S p.1)) p.2

/-- The actual circle coordinate is the selected marked child increment. -/
theorem circleRaw_eq (q : ShapeSpace T σ F) (v : PairParent T σ) :
    circleRaw T σ F P q.val v = ((shapeRealHomeomorph T σ hσ F P S q).1 v : ℂ) := by
  change q.val (P v).b.val = extend T v.val (fun u => q.val u.val) (P v).b.val
  simp [extend, (P v).b.property]

theorem stableRaw_eq (q : ShapeSpace T σ F) (v : FixedParent T σ) (M : StableMarks T σ F v) :
    stableRaw T σ hσ F v M q.val = stableRealHomeomorph T σ hσ F v M
      (fixedFactorHomeomorph T σ hσ F v M ((orbitHomeomorph T σ hσ F q).2 v)) := by
  letI : DecidableEq (Child T v.val.val) := Classical.decEq _
  cases M with
  | height a ha hf =>
    funext j
    cases j with
    | inl p =>
      rcases p with ⟨u, b⟩
      cases b
      · change (q.val u.val.val.val).re = (extend T v.val (fun w => q.val w.val) u.val.val.val).re
        simp [extend, u.val.val.property]
      · change (q.val u.val.val.val).im = (extend T v.val (fun w => q.val w.val) u.val.val.val).im
        simp [extend, u.val.val.property]
    | inr u =>
      change (q.val u.val.val.val).re = (extend T v.val (fun w => q.val w.val) u.val.val.val).re
      simp [extend, u.val.val.property]
  | realPair a b hne ha hb hf =>
    funext j
    cases j with
    | inl p =>
      rcases p with ⟨u, b⟩
      cases b
      · change (q.val u.val.val.val).re = (extend T v.val (fun w => q.val w.val) u.val.val.val).re
        simp [extend, u.val.val.property]
      · change (q.val u.val.val.val).im = (extend T v.val (fun w => q.val w.val) u.val.val.val).im
        simp [extend, u.val.val.property]
    | inr u =>
      change (q.val u.val.val.val).re = (extend T v.val (fun w => q.val w.val) u.val.val.val).re
      simp [extend, u.val.val.property]

/-- Every real free coordinate is the literal real/imaginary projection of an increment. -/
theorem realRaw_eq (q : ShapeSpace T σ F) :
    realRaw T σ hσ F P S q.val = (shapeRealHomeomorph T σ hσ F P S q).2 := by
  funext j
  cases j with
  | inl p =>
    rcases p with ⟨v, u, b⟩
    cases b
    · change (q.val u.val.val).re = (extend T v.val (fun w => q.val w.val) u.val.val).re
      simp [extend, u.val.property]
    · change (q.val u.val.val).im = (extend T v.val (fun w => q.val w.val) u.val.val).im
      simp [extend, u.val.property]
  | inr p => exact congrFun (stableRaw_eq T σ hσ F q p.1 (S p.1)) p.2

/-- Smooth extension of the actual inverse local angle chart. -/
def angleInverseRaw (u : Circle) (z : ℂ) : ℝ := rotatedAnglePotential (u : ℂ)⁻¹ z

theorem angleInverseRaw_eq (u z : Circle) :
    angleInverseRaw u z = (ForestOrthantCharts.angleChart u).symm z := by
  simp only [angleInverseRaw, rotatedAnglePotential, Complex.log_im]
  rfl

theorem angleInverseRaw_slit (u z : Circle) (hz : z ∈ (ForestOrthantCharts.angleChart u).target) :
    (u : ℂ)⁻¹ * (z : ℂ) ∈ Complex.slitPlane := by
  exact hz.2

theorem contDiffAt_angleInverseRaw (u : Circle) (z : ℂ)
    (hz : (u : ℂ)⁻¹ * z ∈ Complex.slitPlane) {ν : ℕ∞ω} : ContDiffAt ℝ ν (angleInverseRaw u) z :=
  (contDiffAt_rotatedAnglePotential hz).of_le le_top

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestShapeProjectionSmooth
