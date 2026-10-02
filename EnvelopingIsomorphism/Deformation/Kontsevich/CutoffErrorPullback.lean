import EnvelopingIsomorphism.Deformation.Kontsevich.CutoffMonomialPullback
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundedLogMonomialCombination
import EnvelopingIsomorphism.Deformation.Kontsevich.RatioCutoffStokes

/-! Naturality of the genuine logarithmic primitive and cutoff error. All local
identifications follow from equalities of complex functions on an open chart. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich
open ContinuousAlternatingMap Set Filter
open scoped Topology BigOperators

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {n : ℕ}

namespace LogRadialPrimitive

/-- Native primitive pullback is functorial under the actual first derivative. -/
theorem primitive_comp (f : Fin (n + 1) → G → ℂ) {F : E → G} {x : E}
    (hF : DifferentiableAt ℝ F x) (hf : ∀ j, DifferentiableAt ℝ (f j) (F x))
    (hf0 : ∀ j, f j (F x) ≠ 0) :
    (primitive f (F x)).compContinuousLinearMap (fderiv ℝ F x) =
      primitive (fun j y ↦ f j (F y)) x := by
  have hlog := (hasFDerivAt_logarithms f hf hf0).differentiableAt
  have hid : logarithms (fun j y ↦ f j (F y)) = logarithms f ∘ F := rfl
  unfold primitive
  rw [hid, fderiv_comp x hlog hF]
  ext v
  rfl

/-- Function identities on a neighborhood determine the native primitive. -/
theorem primitive_congr_of_eventuallyEq (f g : Fin (n + 1) → E → ℂ) {x : E}
    (hid : ∀ j, f j =ᶠ[𝓝 x] g j) : primitive f x = primitive g x := by
  have he : logarithms f =ᶠ[𝓝 x] logarithms g := by
    filter_upwards [eventually_all.mpr hid] with y hy
    funext j
    exact congrArg (fun z : ℂ ↦ Real.log ‖z‖) (hy j)
  simp only [primitive, he.eq_of_nhds, he.fderiv_eq]

end LogRadialPrimitive

/-- Naturality preserves the exact alternating signs and normalization. -/
theorem alternatize_smulRight_pullback (ℓ : G →L[ℝ] ℝ)
    (β : G [⋀^Fin n]→L[ℝ] ℝ) (D : E →L[ℝ] G) :
    (alternatizeUncurryFin (ℓ.smulRight β)).compContinuousLinearMap D =
      alternatizeUncurryFin ((ℓ.comp D).smulRight (β.compContinuousLinearMap D)) := by
  ext v
  simp only [compContinuousLinearMap_apply, alternatizeUncurryFin_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousLinearMap.comp_apply]
  rfl

namespace RatioCutoffStokes
open InteriorFiberAngleSplit NormalCrossingStokes
open BoundedLogMonomialCombination

/-- Pullback of the actual original error term, before local normal forms. -/
theorem cutoffTerm_pullback {N : ℕ} (e : Edges N) (he : ∀ j, (e j).1 ≠ (e j).2)
    {F : E → Space N} {x : E} (hF : DifferentiableAt ℝ F x)
    (hx : F x ∈ shapeConfiguration (N + 1)) (ε : ℝ) :
    (cutoffTerm e ε (F x)).compContinuousLinearMap (fderiv ℝ F x) =
      wedgePrimitive (fderiv ℝ (fun y ↦ RatioCutoff.chi ε (F y)) x)
        (fun j y ↦ edgeFunctions e j (F y)) x := by
  rw [cutoffTerm, alternatize_smulRight_pullback]
  have hb := LogRadialPrimitive.primitive_comp (edgeFunctions e) hF
    (fun j ↦ (hasFDerivAt_shapeDifference _ _ (F x)).differentiableAt)
    (fun j ↦ shapeDifference_ne_zero hx (he j))
  change alternatizeUncurryFin
    (((fderiv ℝ (RatioCutoff.chi ε) (F x)).comp (fderiv ℝ F x)).smulRight
      ((LogRadialPrimitive.primitive (edgeFunctions e) (F x)).compContinuousLinearMap (fderiv ℝ F x))) = _
  rw [hb]
  have hc : fderiv ℝ (fun y ↦ RatioCutoff.chi ε (F y)) x =
      (fderiv ℝ (RatioCutoff.chi ε) (F x)).comp (fderiv ℝ F x) :=
    fderiv_comp x (RatioCutoff.hasFDerivAt_chi_radial ε hx).differentiableAt hF
  rw [← hc]
  rfl

/-- Exact identification with the local determinant density. Only the scalar
complex-function identities are hypotheses; the entire form identity is proved. -/
theorem cutoffTerm_pullback_eq_density {N : ℕ} (e : Edges N)
    (he : ∀ j, (e j).1 ≠ (e j).2)
    {J : Type*} [Fintype J] [DecidableEq J]
    (d : LocalData J (RatioCutoff.RadialIndex (N + 1)) (Degree N))
    {F : (J → ℂ) → Space N} {x : J → ℂ} (hF : DifferentiableAt ℝ F x)
    (hx : F x ∈ shapeConfiguration (N + 1)) (ε : ℝ)
    {U : Set (J → ℂ)} (hU : IsOpen U) (hxU : x ∈ U)
    (hbase : ∀ j, ∀ y ∈ U, edgeFunctions e j (F y) = baseFunctions d j y)
    (hextra : ∀ k, ∀ y ∈ U, RatioCutoff.radialFunction k (F y) = extraFunctions d k y)
    (v : Fin (NormalCrossingStokes.Dim N) → J → ℂ) :
    ((cutoffTerm e ε (F x)).compContinuousLinearMap (fderiv ℝ F x)) v =
      BoundedLogMonomialCombination.density d (RatioCutoff.signedCoefficient ε (F x)) v x := by
  rw [cutoffTerm_pullback e he hF hx ε]
  have hb : LogRadialPrimitive.primitive (fun j y ↦ edgeFunctions e j (F y)) x =
      LogRadialPrimitive.primitive (baseFunctions d) x := by
    apply LogRadialPrimitive.primitive_congr_of_eventuallyEq
    intro j
    filter_upwards [hU.mem_nhds hxU] with y hy
    exact hbase j y hy
  have hd : fderiv ℝ (fun y ↦ RatioCutoff.chi ε (F y)) x =
      combination (RatioCutoff.signedCoefficient ε (F x)) (extraFunctions d) x := by
    rw [RatioCutoff.fderiv_chi_comp_eq_sum_radial hF hx ε]
    unfold combination
    apply Finset.sum_congr rfl
    intro k hk
    have hid : (fun y ↦ RatioCutoff.radialFunction k (F y)) =ᶠ[𝓝 x] extraFunctions d k := by
      filter_upwards [hU.mem_nhds hxU] with y hy
      exact hextra k y hy
    simp only [radialCovector, hid.eq_of_nhds, hid.fderiv_eq]
  simp only [wedgePrimitive, hb, hd, BoundedLogMonomialCombination.density]

end RatioCutoffStokes
end EnvelopingIsomorphism.Deformation.Kontsevich
