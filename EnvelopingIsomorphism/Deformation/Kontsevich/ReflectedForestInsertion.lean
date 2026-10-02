import EnvelopingIsomorphism.Deformation.Kontsevich.ForestInsertionDifference
import Mathlib.Analysis.Complex.Basic

/-!
# Reflection of literal forest insertion formulas

All identities are proved by reindexing the actual ancestor products and
branch sums. They remain valid when radii vanish, and assume no configuration
or positivity predicate.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedForestInsertion

open AncestorScaleRatios ForestInsertionDifference ComplexConjugate
open scoped BigOperators Classical

variable (t : RootedTree) [Fintype t] (σ : t ≃o t)

theorem ancestors_image (v : t) : ancestors (σ v) = (ancestors v).image σ := by
  ext u
  constructor
  · intro hu
    refine Finset.mem_image.mpr ⟨σ.symm u, ?_, σ.apply_symm_apply u⟩
    apply (mem_ancestors _ _).mpr
    have h := σ.symm.monotone ((mem_ancestors _ _).mp hu)
    simpa only [OrderIso.symm_apply_apply] using h
  · rintro hu
    rcases Finset.mem_image.mp hu with ⟨w, hw, rfl⟩
    exact (mem_ancestors _ _).mpr (σ.monotone ((mem_ancestors _ _).mp hw))

theorem erased_ancestors_image (v : t) :
    (ancestors (σ v)).erase ⊥ = ((ancestors v).erase ⊥).image σ := by
  rw [ancestors_image, Finset.image_erase σ.injective, σ.map_bot]

theorem branch_image (c v : t) : branch t (σ c) (σ v) = (branch t c v).image σ := by
  rw [branch, branch, ancestors_image, ancestors_image, Finset.image_sdiff _ _ σ.injective]

section Scales

variable {R : Type*} [CommMonoid R]

/-- Absolute ancestor products are invariant under the actual equivariant radii. -/
theorem scale_reflect (ρ : t → R) (hρ : ∀ u, ρ (σ u) = ρ u) (v : t) :
    scale ρ (σ v) = scale ρ v := by
  rw [scale, scale, ancestors_image, Finset.prod_image σ.injective.injOn]
  apply Finset.prod_congr rfl
  intro u hu
  exact hρ u

/-- The residual products are invariant too, without dividing by an absolute scale. -/
theorem residualScale_reflect (ρ : t → R) (hρ : ∀ u, ρ (σ u) = ρ u) (c v : t) :
    residualScale ρ (σ c) (σ v) = residualScale ρ c v := by
  change (∏ u ∈ branch t (σ c) (σ v), ρ u) = ∏ u ∈ branch t c v, ρ u
  rw [branch_image, Finset.prod_image σ.injective.injOn]
  apply Finset.prod_congr rfl
  intro u hu
  exact hρ u

end Scales

section LinearSymmetry

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Linear symmetry commutes with the literal insertion sum. -/
theorem position_map (ρ : t → R) (hρ : ∀ u, ρ (σ u) = ρ u)
    (a : t → M) (L : M →ₗ[R] M) (ha : ∀ u, a (σ u) = L (a u)) (v : t) :
    position t ρ a (σ v) = L (position t ρ a v) := by
  rw [position, position, erased_ancestors_image, Finset.sum_image σ.injective.injOn, map_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [← σ.map_pred u, scale_reflect t σ ρ hρ, ha, map_smul]

/-- The same reindexing proves symmetry of each actual residual branch sum. -/
theorem branchUnit_map (ρ : t → R) (hρ : ∀ u, ρ (σ u) = ρ u)
    (a : t → M) (L : M →ₗ[R] M) (ha : ∀ u, a (σ u) = L (a u)) (c v : t) :
    branchUnit t ρ a (σ c) (σ v) = L (branchUnit t ρ a c v) := by
  rw [branchUnit, branchUnit, branch_image, Finset.sum_image σ.injective.injOn, map_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [← σ.map_pred u, residualScale_reflect t σ ρ hρ, ha, map_smul]

theorem unitDifference_map (ρ : t → R) (hρ : ∀ u, ρ (σ u) = ρ u)
    (a : t → M) (L : M →ₗ[R] M) (ha : ∀ u, a (σ u) = L (a u)) (v w : t) :
    unitDifference t ρ a (σ v) (σ w) = L (unitDifference t ρ a v w) := by
  rw [unitDifference, ← σ.map_inf v w, branchUnit_map t σ ρ hρ a L ha,
    branchUnit_map t σ ρ hρ a L ha, unitDifference, map_sub]

end LinearSymmetry

section ComplexReflection

variable (ρ : t → ℝ) (hρ : ∀ u, ρ (σ u) = ρ u)
  (a : t → ℂ) (ha : ∀ u, a (σ u) = conj (a u))

include hρ ha

/-- Literal inserted positions reflect by actual complex conjugation. -/
theorem position_reflect (v : t) : position t ρ a (σ v) = conj (position t ρ a v) :=
  position_map t σ ρ hρ a Complex.conjAe.toLinearMap ha v

theorem branchUnit_reflect (c v : t) :
    branchUnit t ρ a (σ c) (σ v) = conj (branchUnit t ρ a c v) :=
  branchUnit_map t σ ρ hρ a Complex.conjAe.toLinearMap ha c v

/-- The actual unit difference is conjugation-equivariant even on zero-radius faces. -/
theorem unitDifference_reflect (v w : t) :
    unitDifference t ρ a (σ v) (σ w) = conj (unitDifference t ρ a v w) :=
  unitDifference_map t σ ρ hρ a Complex.conjAe.toLinearMap ha v w

/-- A fixed node, in particular a fixed boundary leaf, has a real inserted position. -/
theorem position_im_eq_zero_of_fixed (v : t) (hv : σ v = v) : (position t ρ a v).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  have h := position_reflect t σ ρ hρ a ha v
  rw [hv] at h
  exact h.symm

theorem position_eq_ofReal_of_fixed (v : t) (hv : σ v = v) :
    position t ρ a v = ((position t ρ a v).re : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using position_im_eq_zero_of_fixed t σ ρ hρ a ha v hv

/-- The difference of an inserted point and its reflected partner has zero real part. -/
theorem mirrored_difference_re_eq_zero (v : t) :
    (position t ρ a v - position t ρ a (σ v)).re = 0 := by
  rw [position_reflect t σ ρ hρ a ha]
  simp only [Complex.sub_re, Complex.conj_re, sub_self]

theorem mirrored_difference_conj_neg (v : t) :
    conj (position t ρ a v - position t ρ a (σ v)) =
      -(position t ρ a v - position t ρ a (σ v)) := by
  rw [position_reflect t σ ρ hρ a ha, map_sub]
  simp only [starRingEnd_apply, star_star]
  abel

/-- The reflected pair's normalised difference is purely imaginary as well. -/
theorem mirrored_unitDifference_conj_neg (hσ : Function.Involutive σ) (v : t) :
    conj (unitDifference t ρ a v (σ v)) = -unitDifference t ρ a v (σ v) := by
  rw [← unitDifference_reflect t σ ρ hρ a ha, hσ v]
  simp only [unitDifference, inf_comm (σ v) v]
  abel

theorem mirrored_unitDifference_re_eq_zero (hσ : Function.Involutive σ) (v : t) :
    (unitDifference t ρ a v (σ v)).re = 0 := by
  have h := congrArg Complex.re (mirrored_unitDifference_conj_neg t σ ρ hρ a ha hσ v)
  simp only [Complex.conj_re, Complex.neg_re] at h
  linarith

end ComplexReflection

end EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedForestInsertion
