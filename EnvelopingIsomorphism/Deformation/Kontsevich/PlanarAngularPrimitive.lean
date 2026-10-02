import EnvelopingIsomorphism.Deformation.Kontsevich.RatioCutoffStokes

/-! The actual affine point differences have complex-linear derivatives.
The native primitive differentiates to the angular shape density with the
same interleaved 1,I orientation and no additional sign. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich
open ContinuousAlternatingMap

namespace InteriorFiberAngleSplit

/-- The derivative of each fixed or free point, over the complex scalars. -/
def pointComplexLinear {N : ℕ} : Point N → Shape N →L[ℂ] ℂ :=
  Matrix.vecCons 0 (Matrix.vecCons 0 (fun j ↦
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N ↦ ℂ) j)))

theorem pointComplexLinear_restrictScalars {N : ℕ} (j : Point N) :
    (pointComplexLinear j).restrictScalars ℝ = pointLinear j := by
  refine Fin.cases ?_ (fun k ↦ Fin.cases ?_ (fun l ↦ ?_) k) j
  all_goals ext v; rfl

def shapeComplexDerivative {N : ℕ} (s t : Point N) : Shape N →ₗ[ℂ] ℂ :=
  (pointComplexLinear t - pointComplexLinear s).toLinearMap

theorem shapeComplexDerivative_restrictScalars {N : ℕ} (s t : Point N) :
    (shapeComplexDerivative s t).toContinuousLinearMap.restrictScalars ℝ = shapeDerivative s t := by
  ext v
  have ht := congrArg (fun D : Shape N →L[ℝ] ℂ ↦ D v) (pointComplexLinear_restrictScalars t)
  have hs := congrArg (fun D : Shape N →L[ℝ] ℂ ↦ D v) (pointComplexLinear_restrictScalars s)
  change pointComplexLinear t v = pointLinear t v at ht
  change pointComplexLinear s v = pointLinear s v at hs
  change pointComplexLinear t v - pointComplexLinear s v = pointLinear t v - pointLinear s v
  rw [ht, hs]

theorem hasFDerivAt_shapeDifference_complex {N : ℕ} (s t : Point N) (η : Shape N) :
    HasFDerivAt (shapeDifference s t)
      ((shapeComplexDerivative s t).toContinuousLinearMap.restrictScalars ℝ) η := by
  rw [shapeComplexDerivative_restrictScalars]
  exact hasFDerivAt_shapeDifference s t η

end InteriorFiberAngleSplit

namespace RatioCutoffStokes
open InteriorFiberAngleSplit NormalCrossingStokes

/-- Only the notation of the real dimension changes. Both frames retain their order. -/
def angularIndex (N : ℕ) : Fin (InteriorFiberAngleSplit.Dim (N + 1)) ≃ Fin (NormalCrossingStokes.Dim N) :=
  finCongr (by dsimp [NormalCrossingStokes.Dim, Degree, InteriorFiberAngleSplit.Dim,
    AngularRadial.realDimension]; omega)

def angularEdges {N : ℕ} (e : Edges N) : InteriorFiberAngleSplit.Edges (N + 1) :=
  fun j ↦ e (angularIndex N j)

theorem actualFrame_angularIndex (N : ℕ) (j : Fin (InteriorFiberAngleSplit.Dim (N + 1))) :
    actualFrame N (angularIndex N j) = AngularRadial.realBasis (N + 1) j := by
  simp [actualFrame, angularIndex]

/-- The derivative of the actual primitive is the actual angular determinant
in the exact original real frame, with no holomorphic-form premise. -/
theorem extDeriv_beta_actualFrame_eq_shapeDensity {N : ℕ} (e : Edges N)
    (he : ∀ j, (e j).1 ≠ (e j).2) {η : Space N}
    (hη : η ∈ shapeConfiguration (N + 1)) :
    extDeriv (beta e) η (actualFrame N) = shapeDensity (angularEdges e) η := by
  have hdim : Degree N + 1 = (N + 1) * 2 := by
    dsimp [Degree]
    omega
  have h := LogRadialPrimitive.extDeriv_primitive_angular_apply hdim (edgeFunctions e)
    (fun j ↦ shapeComplexDerivative (e j).1 (e j).2)
    (fun j ↦ ((contDiff_normalizedPoint (e j).2).sub
      (contDiff_normalizedPoint (e j).1)).contDiffAt)
    (fun j ↦ shapeDifference_ne_zero hη (he j))
    (fun j ↦ hasFDerivAt_shapeDifference_complex _ _ η) (actualFrame N)
  change extDeriv (beta e) η (actualFrame N) = _ at h
  rw [h, shapeDensity_eq_det]
  have hr := Matrix.det_submatrix_equiv_self (angularIndex N)
    (fun r c : Fin (NormalCrossingStokes.Dim N) ↦
      ((angularForm (edgeFunctions e c η)).compContinuousLinearMap
        ((shapeComplexDerivative (e c).1 (e c).2).toContinuousLinearMap.restrictScalars ℝ))
          (fun _ : Fin 1 ↦ actualFrame N r))
  rw [← hr]
  congr 1
  funext r c
  simp only [Matrix.submatrix_apply, shapeComplexDerivative_restrictScalars,
    actualFrame_angularIndex, angularEdges, shapeEdgeForm, fderiv_shapeDifference, edgeFunctions]

/-- The cutoff removes the nonconfiguration locus, so the weighted identity
holds on the whole original coordinate space. -/
theorem chi_mul_extDeriv_eq_chi_mul_shapeDensity {N : ℕ} (e : Edges N)
    (he : ∀ j, (e j).1 ≠ (e j).2) {ε : ℝ} (hε : 0 < ε) (η : Space N) :
    RatioCutoff.chi ε η * extDeriv (beta e) η (actualFrame N) =
      RatioCutoff.chi ε η * shapeDensity (angularEdges e) η := by
  by_cases hη : η ∈ shapeConfiguration (N + 1)
  · rw [extDeriv_beta_actualFrame_eq_shapeDensity e he hη]
  · have hc : RatioCutoff.chi ε η = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hs ↦ hη (RatioCutoff.tsupport_chi_subset hε hs))
    simp only [hc, zero_mul]

end RatioCutoffStokes
end EnvelopingIsomorphism.Deformation.Kontsevich
