import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Dimension and rank vanishing for actual alternating pullbacks

The algebraic statement uses linear dependence of the arguments. Continuous
and differentiable pullbacks then inherit the result. In particular, a form
of the total dimension of `Coarse × Shape` vanishes when its pullback factors
through the coarse coordinates and the shape dimension is positive.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

section Algebraic

variable {k E F G : Type*} [Field k]
  [AddCommGroup E] [Module k E] [AddCommGroup F] [Module k F]
  [AddCommGroup G] [Module k G] {r : ℕ}

/-- An alternating form above the dimension of its source is zero. -/
theorem alternating_eq_zero_of_finrank_lt [FiniteDimensional k E]
    (ω : E [⋀^Fin r]→ₗ[k] G) (hr : Module.finrank k E < r) : ω = 0 := by
  apply AlternatingMap.ext
  intro v
  apply ω.map_linearDependent
  intro hv
  have hc : r ≤ Module.finrank k E := by simpa only [Fintype.card_fin] using hv.fintype_card_le_finrank
  exact (Nat.not_le_of_lt hr) hc

/-- A finite-rank linear map annihilates alternating forms of higher degree. -/
theorem alternating_pullback_eq_zero_of_finrank_range_lt
    (A : E →ₗ[k] F) [FiniteDimensional k (LinearMap.range A)]
    (ω : F [⋀^Fin r]→ₗ[k] G) (hr : Module.finrank k (LinearMap.range A) < r) :
    ω.compLinearMap A = 0 := by
  have h := alternating_eq_zero_of_finrank_lt (ω.compLinearMap (LinearMap.range A).subtype) hr
  apply AlternatingMap.ext
  intro v
  exact congrArg (fun η : LinearMap.range A [⋀^Fin r]→ₗ[k] G =>
    η (fun i => A.rangeRestrict (v i))) h

end Algebraic

section Continuous

variable {k E F G C S : Type*} [NontriviallyNormedField k]
  [NormedAddCommGroup E] [NormedSpace k E]
  [NormedAddCommGroup F] [NormedSpace k F]
  [NormedAddCommGroup G] [NormedSpace k G]
  [NormedAddCommGroup C] [NormedSpace k C]
  [NormedAddCommGroup S] [NormedSpace k S] {r : ℕ}

/-- Continuous alternating forms obey the same genuine dimension bound. -/
theorem continuousAlternating_eq_zero_of_finrank_lt [FiniteDimensional k E]
    (ω : E [⋀^Fin r]→L[k] G) (hr : Module.finrank k E < r) : ω = 0 := by
  have h := alternating_eq_zero_of_finrank_lt ω.toAlternatingMap hr
  apply ContinuousAlternatingMap.ext
  intro v
  exact congrArg (fun η : E [⋀^Fin r]→ₗ[k] G => η v) h

/-- Pullback through a continuous linear map of rank below the form degree is zero. -/
theorem continuousAlternating_pullback_eq_zero_of_finrank_range_lt
    (A : E →L[k] F) [FiniteDimensional k (LinearMap.range A.toLinearMap)]
    (ω : F [⋀^Fin r]→L[k] G) (hr : Module.finrank k (LinearMap.range A.toLinearMap) < r) :
    ω.compContinuousLinearMap A = 0 := by
  have h := alternating_pullback_eq_zero_of_finrank_range_lt A.toLinearMap ω.toAlternatingMap hr
  apply ContinuousAlternatingMap.ext
  intro v
  exact congrArg (fun η : E [⋀^Fin r]→ₗ[k] G => η v) h

/-- Factoring through a smaller-dimensional vector space forces the actual pullback to vanish. -/
theorem continuousAlternating_comp_eq_zero_of_finrank_lt [FiniteDimensional k C]
    (ω : F [⋀^Fin r]→L[k] G) (A : E →L[k] C) (B : C →L[k] F)
    (hr : Module.finrank k C < r) : ω.compContinuousLinearMap (B.comp A) = 0 := by
  have h := continuousAlternating_eq_zero_of_finrank_lt (ω.compContinuousLinearMap B) hr
  apply ContinuousAlternatingMap.ext
  intro v
  exact congrArg (fun η : C [⋀^Fin r]→L[k] G => η (fun i => A (v i))) h

/-- Direct projection version, without any finite-dimensional assumption on the shape factor. -/
theorem continuousAlternating_fst_pullback_eq_zero_of_finrank_lt [FiniteDimensional k C]
    (ω : C [⋀^Fin r]→L[k] G) (hr : Module.finrank k C < r) :
    ω.compContinuousLinearMap (ContinuousLinearMap.fst k C S) = 0 := by
  rw [continuousAlternating_eq_zero_of_finrank_lt ω hr]
  ext v
  rfl

/-- Chain rule plus the actual dimension bound for a differentiable factorization. -/
theorem alternating_pullback_comp_eq_zero_of_finrank_lt [FiniteDimensional k C]
    (ω : F → F [⋀^Fin r]→L[k] G) {p : E → C} {g : C → F} {x : E}
    (hp : DifferentiableAt k p x) (hg : DifferentiableAt k g (p x))
    (hr : Module.finrank k C < r) :
    (ω ((g ∘ p) x)).compContinuousLinearMap (fderiv k (g ∘ p) x) = 0 := by
  rw [fderiv_comp x hg hp]
  exact continuousAlternating_comp_eq_zero_of_finrank_lt _ _ _ hr

/-- Top-degree forms pulled back from coarse coordinates vanish along a positive-dimensional
shape factor. The displayed pullback is the actual Fréchet derivative of the composite. -/
theorem alternating_pullback_prod_fst_top_eq_zero [FiniteDimensional k C]
    [FiniteDimensional k S] (hS : 0 < Module.finrank k S)
    (ω : F → F [⋀^Fin (Module.finrank k C + Module.finrank k S)]→L[k] G)
    {g : C → F} {x : C × S} (hg : DifferentiableAt k g x.1) :
    (ω (g x.1)).compContinuousLinearMap (fderiv k (g ∘ Prod.fst) x) = 0 := by
  apply alternating_pullback_comp_eq_zero_of_finrank_lt ω differentiableAt_fst hg
  omega

/-- The same vanishing with the form degree written as the full product dimension. -/
theorem alternating_pullback_prod_fst_finrank_eq_zero [FiniteDimensional k C]
    [FiniteDimensional k S] (hS : 0 < Module.finrank k S)
    (ω : F → F [⋀^Fin (Module.finrank k (C × S))]→L[k] G)
    {g : C → F} {x : C × S} (hg : DifferentiableAt k g x.1) :
    (ω (g x.1)).compContinuousLinearMap (fderiv k (g ∘ Prod.fst) x) = 0 := by
  apply alternating_pullback_comp_eq_zero_of_finrank_lt ω differentiableAt_fst hg
  rw [Module.finrank_prod]
  omega

/-- A proved factorization of the coordinate map suffices; no vanishing premise is supplied. -/
theorem alternating_pullback_factor_prod_top_eq_zero [FiniteDimensional k C]
    [FiniteDimensional k S] (hS : 0 < Module.finrank k S)
    (ω : F → F [⋀^Fin (Module.finrank k (C × S))]→L[k] G)
    {f : C × S → F} {g : C → F} (hf : f = g ∘ Prod.fst)
    {x : C × S} (hg : DifferentiableAt k g x.1) :
    (ω (f x)).compContinuousLinearMap (fderiv k f x) = 0 := by
  subst f
  exact alternating_pullback_prod_fst_finrank_eq_zero hS ω hg

/-- A coarse form of total product degree already vanishes, hence so does its projection pullback. -/
theorem continuousAlternating_coarse_top_pullback_eq_zero [FiniteDimensional k C]
    [FiniteDimensional k S] (hS : 0 < Module.finrank k S)
    (ω : C [⋀^Fin (Module.finrank k C + Module.finrank k S)]→L[k] G) :
    ω.compContinuousLinearMap (ContinuousLinearMap.fst k C S) = 0 := by
  have h := continuousAlternating_eq_zero_of_finrank_lt ω (by omega)
  rw [h]
  ext v
  rfl

end Continuous

end EnvelopingIsomorphism.Deformation.Kontsevich
