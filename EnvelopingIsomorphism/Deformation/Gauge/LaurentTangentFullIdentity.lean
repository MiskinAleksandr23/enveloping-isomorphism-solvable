import EnvelopingIsomorphism.Deformation.Gauge.LaurentTaylorFullIdentity
import EnvelopingIsomorphism.Deformation.Gauge.MixedGraphTaylorCoefficients
import EnvelopingIsomorphism.Deformation.Gauge.TaylorNaturality
import EnvelopingIsomorphism.FormalSeries.BinaryAssociator

/-! All-placement tangent evaluation is the actual full graph operator family
applied to its independent Laurent direction. -/

noncomputable section
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Gauge.LaurentTangentFullIdentity
open EnvelopingIsomorphism.FormalSeries PowerSeriesModule

universe u
variable {k V D O : Type u} [Field k]
  [AddCommGroup V] [Module k V] [AddCommGroup D] [Module k D] [AddCommGroup O] [Module k O]

private theorem linearApply_map_eq
    {R A B C : Type*} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B →ₗ[R] C) (P : PowerSeriesModule R A) (Y : PowerSeriesModule R B) :
    linearApply (map f P) Y = applyBilinear f P Y := by
  apply PowerSeriesModule.ext
  intro n
  simp only [coeffV_linearApply, coeffV_map, coeffV_applyBilinear]

/-- No Laurent positivity is imposed on either β's coefficients or the
direction Y. Only the original positive-t perturbation premise is used. -/
theorem tangentApply_eq_fullEvaluation
    (C : GraphTaylorFamily (k := k) (V := V) (W := D →ₗ[k] O)) (π₀ : V)
    (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : coeffV 0 β = 0)
    (Y : PowerSeriesModule (LaurentSeries k) (LaurentModule k D)) :
    tangentApply (MixedGraphTaylorCoefficients.tangentFamily C π₀) β Y =
      applyBilinear LaurentModule.linearApply
        (LaurentFullGraphEvaluation.fullEvaluation C π₀ β hβ) Y := by
  have hh : (MixedGraphTaylorCoefficients.tangentFamily C π₀).higher =
      mapTaylorFamily LaurentModule.linearApply (laurentPlacementTaylorFamily C π₀) := rfl
  rw [tangentApply, hh, ← map_taylorApply, linearApply_map_eq,
    LaurentTaylorFullIdentity.fullEvaluation_eq_base_add_taylor]
  have hadd : applyBilinear LaurentModule.linearApply
      (single 0 (MiddleExactPerturbation.toLaurent (baseMCImage C π₀)) +
        taylorApply (laurentPlacementTaylorFamily C π₀) β) Y =
      applyBilinear LaurentModule.linearApply
        (single 0 (MiddleExactPerturbation.toLaurent (baseMCImage C π₀))) Y +
      applyBilinear LaurentModule.linearApply
        (taylorApply (laurentPlacementTaylorFamily C π₀) β) Y := by
    exact congrArg (fun F ↦ F Y) ((PowerSeriesModule.extendBilinear
      (LaurentModule.linearApply (k := k) (V := D) (W := O))).map_add _ _)
  rw [hadd, applyBilinear_single_zero_left]
  rfl

end EnvelopingIsomorphism.Deformation.Gauge.LaurentTangentFullIdentity
