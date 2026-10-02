import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Smooth pullback of a fixed alternating form by a varying continuous linear map.
Finite alternatization gives an actual continuous linear retraction from multilinear maps.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open scoped BigOperators

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The signed finite permutation sum, as an actual continuous linear operator. -/
def alternatingSumCLM (r : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin r ↦ E) G →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin r ↦ E) G :=
  ∑ σ : Equiv.Perm (Fin r), Equiv.Perm.sign σ •
    (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E G σ).toContinuousLinearEquiv.toContinuousLinearMap

theorem alternatingSumCLM_apply (r : ℕ)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin r ↦ E) G) :
    alternatingSumCLM r f = f.alternatization.toContinuousMultilinearMap := by
  ext v
  simp [alternatingSumCLM, ContinuousMultilinearMap.alternatization,
    ContinuousMultilinearMap.domDomCongrₗᵢ]

/-- Continuous linear alternatization, with alternating codomain proved from the finite sum. -/
def alternatizationCLM (r : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin r ↦ E) G →L[ℝ] E [⋀^Fin r]→L[ℝ] G :=
  ContinuousAlternatingMap.liftCLM (alternatingSumCLM r) (by
    intro f v i j hv hij
    rw [alternatingSumCLM_apply]
    exact f.alternatization.map_eq_zero_of_eq v hv hij)

theorem alternatizationCLM_apply (r : ℕ)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin r ↦ E) G) :
    alternatizationCLM r f = f.alternatization := by
  ext v
  exact congrArg (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin r ↦ E) G ↦ T v)
    (alternatingSumCLM_apply r f)

theorem alternatizationCLM_on_alternating (r : ℕ) (ω : E [⋀^Fin r]→L[ℝ] G) :
    alternatizationCLM r ω.toContinuousMultilinearMap = r.factorial • ω := by
  rw [alternatizationCLM_apply]
  ext v
  have h := congrArg (fun a : E [⋀^Fin r]→ₗ[ℝ] G ↦ a v)
    (AlternatingMap.coe_alternatization ω.toAlternatingMap)
  change (ContinuousMultilinearMap.alternatization ω.toContinuousMultilinearMap).toAlternatingMap v =
    r.factorial • ω.toAlternatingMap v
  rw [ContinuousMultilinearMap.alternatization_apply_toAlternatingMap]
  simpa only [Fintype.card_fin, AlternatingMap.smul_apply] using h

/-- Normalized alternatization retracts the inclusion of alternating maps. -/
def alternatingProjection (r : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin r ↦ E) G →L[ℝ] E [⋀^Fin r]→L[ℝ] G :=
  (r.factorial : ℝ)⁻¹ • alternatizationCLM r

@[simp] theorem alternatingProjection_on_alternating (r : ℕ) (ω : E [⋀^Fin r]→L[ℝ] G) :
    alternatingProjection r ω.toContinuousMultilinearMap = ω := by
  rw [alternatingProjection, smul_apply, alternatizationCLM_on_alternating,
    ← Nat.cast_smul_eq_nsmul ℝ]
  exact inv_smul_smul₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)) ω

/-- Pullback of a fixed alternating form depends smoothly on its linear argument. -/
theorem contDiff_compContinuousLinearMap {r : ℕ} (ω : F [⋀^Fin r]→L[ℝ] G) :
    ContDiff ℝ ⊤ (fun A : E →L[ℝ] F ↦ ω.compContinuousLinearMap A) := by
  let C : ContinuousMultilinearMap ℝ (fun _ : Fin r ↦ E →L[ℝ] F)
      (ContinuousMultilinearMap ℝ (fun _ : Fin r ↦ E) G) :=
    ContinuousMultilinearMap.compContinuousLinearMapLRight ω.toContinuousMultilinearMap
  have hd : ContDiff ℝ ⊤ (fun A : E →L[ℝ] F ↦ fun _ : Fin r ↦ A) :=
    contDiff_pi.mpr (fun _ ↦ contDiff_id)
  have hm : ContDiff ℝ ⊤ (fun A : E →L[ℝ] F ↦
      ω.toContinuousMultilinearMap.compContinuousLinearMap (fun _ : Fin r ↦ A)) :=
    C.contDiff.comp hd
  have hp := (alternatingProjection (E := E) (G := G) r).contDiff.comp hm
  convert hp using 1
  funext A
  exact (alternatingProjection_on_alternating r (ω.compContinuousLinearMap A)).symm

end EnvelopingIsomorphism.Deformation.Kontsevich
