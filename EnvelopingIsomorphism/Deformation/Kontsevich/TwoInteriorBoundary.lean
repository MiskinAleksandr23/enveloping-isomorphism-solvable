import EnvelopingIsomorphism.Deformation.Kontsevich.LinearCollisionLimits
import EnvelopingIsomorphism.Deformation.Kontsevich.TwoInteriorCollision
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The two-interior collision circle inside the actual compact closure

The doubled coordinates of `I, I+r*u` have constant base and linear velocity.
The general collision-limit theorem puts their explicit limit in the compact
closure and retains the direction `u` on the colliding pair.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration ComplexConjugate Filter Topology
open scoped Topology

def twoInteriorBase : DoubledLabel 2 0 → ℂ
  | Sum.inl (Sum.inl _) => Complex.I
  | Sum.inl (Sum.inr j) => Fin.elim0 j
  | Sum.inr _ => -Complex.I

def twoInteriorVelocity (u : Circle) : DoubledLabel 2 0 → ℂ
  | Sum.inl (Sum.inl i) => if i = 0 then 0 else (u : ℂ)
  | Sum.inl (Sum.inr j) => Fin.elim0 j
  | Sum.inr i => if i = 0 then 0 else conj (u : ℂ)

@[fun_prop] theorem continuous_twoInteriorVelocity (v : DoubledLabel 2 0) :
    Continuous (fun u : Circle => twoInteriorVelocity u v) := by
  cases v with
  | inl v =>
    cases v with
    | inl i =>
      simp only [twoInteriorVelocity]
      split_ifs <;> fun_prop
    | inr j => exact Fin.elim0 j
  | inr i =>
    simp only [twoInteriorVelocity]
    split_ifs <;> fun_prop

theorem twoInterior_doubledPoint (r : ℝ) (u : Circle) (hr : 0 < r) (hr1 : r < 1)
    (v : DoubledLabel 2 0) :
    (twoInteriorNormalized r u hr hr1).val.doubledPoint v =
      twoInteriorBase v + (r : ℂ) * twoInteriorVelocity u v := by
  cases v with
  | inl v =>
    cases v with
    | inl j =>
      fin_cases j <;> simp [twoInteriorNormalized, doubledPoint, vertexPoint,
        twoInteriorBase, twoInteriorVelocity]
    | inr j => exact Fin.elim0 j
  | inr j =>
    fin_cases j <;> simp [twoInteriorNormalized, doubledPoint, twoInteriorBase, twoInteriorVelocity]

theorem twoInteriorVelocity_difference_ne_zero (u : Circle) (p : DoubledPair 2 0)
    (hbase : twoInteriorBase p.val.2 - twoInteriorBase p.val.1 = 0) :
    twoInteriorVelocity u p.val.2 - twoInteriorVelocity u p.val.1 ≠ 0 := by
  let c := twoInteriorNormalized (1 / 2) u (by norm_num) (by norm_num)
  have hp : c.val.pairDifference p = (twoInteriorBase p.val.2 - twoInteriorBase p.val.1) +
      ((1 / 2 : ℝ) : ℂ) * (twoInteriorVelocity u p.val.2 - twoInteriorVelocity u p.val.1) := by
    rw [pairDifference, twoInterior_doubledPoint, twoInterior_doubledPoint]
    ring
  intro hv
  apply c.val.pairDifference_ne_zero p
  rw [hp, hbase, hv]
  simp

def twoInteriorCollisionScale (k : ℕ) : ℝ := 1 / ((k : ℝ) + 2)

theorem twoInteriorCollisionScale_pos (k : ℕ) : 0 < twoInteriorCollisionScale k := by
  unfold twoInteriorCollisionScale
  positivity

theorem twoInteriorCollisionScale_lt_one (k : ℕ) : twoInteriorCollisionScale k < 1 := by
  unfold twoInteriorCollisionScale
  apply (div_lt_one (by positivity)).mpr
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith

theorem tendsto_twoInteriorCollisionScale : Tendsto twoInteriorCollisionScale atTop (𝓝 0) := by
  have h := (tendsto_add_atTop_iff_nat 2).mpr (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  change Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 2)) atTop (𝓝 0)
  simpa only [Nat.cast_add, Nat.cast_ofNat] using h

def twoInteriorCollisionSequence (u : Circle) (k : ℕ) : Normalized (0 : Fin 2) 0 :=
  twoInteriorNormalized (twoInteriorCollisionScale k) u (twoInteriorCollisionScale_pos k)
    (twoInteriorCollisionScale_lt_one k)

theorem twoInteriorBoundaryCoordinates_mem (u : Circle) :
    linearCollisionCoordinates twoInteriorBase (twoInteriorVelocity u) ∈
      compactificationSet (0 : Fin 2) 0 :=
  linearCollisionCoordinates_mem_compactification (twoInteriorCollisionSequence u) twoInteriorBase
    (twoInteriorVelocity u) tendsto_twoInteriorCollisionScale
    (Eventually.of_forall twoInteriorCollisionScale_pos)
    (fun _ v => twoInterior_doubledPoint _ u _ _ v)

/-- The retained boundary point for the direction `u`. -/
def twoInteriorBoundaryPoint (u : Circle) : Compactification (0 : Fin 2) 0 :=
  ⟨linearCollisionCoordinates twoInteriorBase (twoInteriorVelocity u), twoInteriorBoundaryCoordinates_mem u⟩

@[fun_prop] theorem continuous_twoInteriorBoundaryPoint : Continuous twoInteriorBoundaryPoint :=
  (continuous_linearCollisionCoordinates twoInteriorBase twoInteriorVelocity
    continuous_twoInteriorVelocity twoInteriorVelocity_difference_ne_zero).subtype_mk _

theorem tendsto_twoInteriorBoundaryPoint (u : Circle) :
    Tendsto (fun k => compactificationEmbedding (0 : Fin 2) (twoInteriorCollisionSequence u k))
      atTop (𝓝 (twoInteriorBoundaryPoint u)) := by
  apply tendsto_subtype_rng.mpr
  exact tendsto_compactCoordinates_linear (twoInteriorCollisionSequence u) twoInteriorBase
    (twoInteriorVelocity u) tendsto_twoInteriorCollisionScale
    (Eventually.of_forall twoInteriorCollisionScale_pos)
    (fun k v => twoInterior_doubledPoint _ u _ _ v)

/-- The radial limit holds for every positive scale family tending to zero. -/
theorem tendsto_twoInteriorBoundaryPoint_of_scale {α : Type*} {l : Filter α}
    (r : α → ℝ) (u : Circle) (hr : ∀ x, 0 < r x) (hr1 : ∀ x, r x < 1)
    (hzero : Tendsto r l (𝓝 0)) :
    Tendsto (fun x => compactificationEmbedding (0 : Fin 2)
      (twoInteriorNormalized (r x) u (hr x) (hr1 x))) l (𝓝 (twoInteriorBoundaryPoint u)) := by
  apply tendsto_subtype_rng.mpr
  exact tendsto_compactCoordinates_linear (fun x => twoInteriorNormalized (r x) u (hr x) (hr1 x))
    twoInteriorBase (twoInteriorVelocity u) hzero (Eventually.of_forall hr)
    (fun x v => twoInterior_doubledPoint _ u _ _ v)

def twoInteriorCollidingPair : DoubledPair 2 0 :=
  harmonicNumeratorPair (0 : Fin 2) (Sum.inl 1) (by decide)

/-- The compactification retains the full circular collision direction. -/
theorem twoInteriorBoundaryPoint_direction (u : Circle) :
    (twoInteriorBoundaryPoint u).val.2.1 twoInteriorCollidingPair = u := by
  simp [twoInteriorBoundaryPoint, linearCollisionCoordinates, twoInteriorCollidingPair,
    harmonicNumeratorPair, linearPhaseLimit, twoInteriorBase, twoInteriorVelocity,
    complexPhase_circle]

theorem twoInteriorBoundaryPoint_injective : Function.Injective twoInteriorBoundaryPoint := by
  intro u v h
  have hd := congrArg (fun x : Compactification (0 : Fin 2) 0 => x.val.2.1 twoInteriorCollidingPair) h
  simpa only [twoInteriorBoundaryPoint_direction] using hd

theorem isClosedEmbedding_twoInteriorBoundaryPoint : IsClosedEmbedding twoInteriorBoundaryPoint :=
  continuous_twoInteriorBoundaryPoint.isClosedEmbedding twoInteriorBoundaryPoint_injective

/-- These points are genuinely added by compactification, not original distinct-point configurations. -/
theorem twoInteriorBoundaryPoint_not_mem_range (u : Circle) :
    twoInteriorBoundaryPoint u ∉ Set.range
      (compactificationEmbedding (0 : Fin 2) : Normalized (0 : Fin 2) 0 → Compactification (0 : Fin 2) 0) := by
  rintro ⟨c, hc⟩
  have hpos := congrArg (fun x : Compactification (0 : Fin 2) 0 =>
    x.val.1 (Sum.inl (1 : Fin 2))) hc
  have hi : c.val.interior 1 = UpperHalfPlane.I := by
    apply UpperHalfPlane.ext
    apply OnePoint.coe_injective
    exact hpos
  have heq : (1 : Fin 2) = 0 := c.val.interior_injective (hi.trans c.property.symm)
  norm_num at heq

theorem twoInteriorBoundaryPoint_phase (u : Circle) :
    (extendedHarmonicPhase (0 : Fin 2) (Sum.inl 1) (by decide) (twoInteriorBoundaryPoint u) : ℂ) =
      (u : ℂ) / Complex.I := by
  change (((twoInteriorBoundaryPoint u).val.2.1 twoInteriorCollidingPair /
    (twoInteriorBoundaryPoint u).val.2.1 (harmonicDenominatorPair (0 : Fin 2) (Sum.inl 1)) : Circle) : ℂ) =
      (u : ℂ) / Complex.I
  rw [twoInteriorBoundaryPoint_direction]
  have hden : (twoInteriorBoundaryPoint u).val.2.1 (harmonicDenominatorPair (0 : Fin 2) (Sum.inl 1)) =
      complexPhase ((2 : ℂ) * Complex.I) := by
    simp [twoInteriorBoundaryPoint, linearCollisionCoordinates, harmonicDenominatorPair,
      linearPhaseLimit, twoInteriorBase, twoInteriorVelocity, two_mul]
  have hphase : complexPhase ((2 : ℂ) * Complex.I) = complexPhase Complex.I :=
    complexPhase_pos_real_mul (r := 2) (by norm_num) Complex.I
  rw [hden, hphase, Circle.coe_div,
    complexPhase_coe Complex.I_ne_zero]
  simp

/-- The continuous phase on the compact closure agrees with the phase of the smooth
regularized collision formula at the added circle. -/
theorem twoInteriorBoundaryPoint_phase_eq_regularized (u : Circle) :
    extendedHarmonicPhase (0 : Fin 2) (Sum.inl 1) (by decide) (twoInteriorBoundaryPoint u) =
      complexPhase (twoInteriorRegularizedRatio (0, (u : ℂ))) := by
  apply Circle.ext
  rw [twoInteriorBoundaryPoint_phase, complexPhase_twoInteriorRegularizedRatio_zero]

end EnvelopingIsomorphism.Deformation.Kontsevich
