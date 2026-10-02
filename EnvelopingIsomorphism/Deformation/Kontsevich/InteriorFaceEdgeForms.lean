import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFaceDRCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.AngularPhasePullback

/-! Literal simple interior-face edge forms from retained doubled-pair units. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFaceEdgeForms
open Configuration InteriorGraphFaceCoordinates InteriorFaceDRCoordinates ClusterAngularCoordinates
open scoped Classical
variable {n m : ℕ} {i a b : Fin n} {S : Finset (Fin n)}

@[simp] theorem denominator_mask (j : Fin n) (v : Fin n ⊕ Fin m) :
    ¬ clusterPairCollapses S (harmonicDenominatorPair j v) := by cases v <;> simp [clusterPairCollapses, harmonicDenominatorPair]

@[simp] theorem numerator_internal_mask (j k : Fin n) (h : Sum.inl k ≠ (Sum.inl j : Fin n ⊕ Fin m)) :
    clusterPairCollapses S (harmonicNumeratorPair j (Sum.inl k) h) ↔ j ∈ S ∧ k ∈ S := Iff.rfl

@[simp] theorem numerator_boundary_mask (j : Fin n) (k : Fin m) (h : Sum.inr k ≠ (Sum.inl j : Fin n ⊕ Fin m)) :
    ¬ clusterPairCollapses S (harmonicNumeratorPair j (Sum.inr k) h) := by simp [clusterPairCollapses, harmonicNumeratorPair]

def pairForm (p : DoubledPair n m) (y : ProductCoordinates i a b S m) :
    ProductCoordinates i a b S m [⋀^Fin 1]→L[ℝ] ℝ := angularPullback (unit p) y

def edgeForm (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j) (y : ProductCoordinates i a b S m) :
    ProductCoordinates i a b S m [⋀^Fin 1]→L[ℝ] ℝ :=
  pairForm (harmonicNumeratorPair j v hv) y - pairForm (harmonicDenominatorPair j v) y

theorem ratio_internal (j k : Fin n) (hv : Sum.inl k ≠ (Sum.inl j : Fin n ⊕ Fin m))
    (hj : j ∈ S) (hk : k ∈ S) :
    (fun y : ProductCoordinates i a b S m ↦ unit (harmonicNumeratorPair j (Sum.inl k) hv) y /
      unit (harmonicDenominatorPair j (Sum.inl k)) y) = internalRatio j k ∘ toAngular := by
  funext y
  simp only [unit, numerator_internal_mask, hj, hk, and_self, if_true, denominator_mask, if_false]
  change ((toAngular y).toFree.velocity k - (toAngular y).toFree.velocity j) /
      ((toAngular y).toFree.base k - starRingEnd ℂ ((toAngular y).toFree.base j)) = _
  rw [(toAngular y).toFree.base_eq_of_same (Or.inr ⟨hk, hj⟩)]
  simp only [Function.comp_apply, internalRatio, variableInternalClusterRegularizedRatio,
    variableInternalClusterDenominator, internalParameters, radius_toAngular, Complex.ofReal_zero,
    zero_mul, add_zero]

theorem ratio_external (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j)
    (hc : ¬ clusterPairCollapses S (harmonicNumeratorPair j v hv)) :
    (fun y : ProductCoordinates i a b S m ↦ unit (harmonicNumeratorPair j v hv) y /
      unit (harmonicDenominatorPair j v) y) =
      (fun q : ClusterAngularCoordinates i a b S m ↦ harmonicRatio (actualPair j v q).1 (actualPair j v q).2) ∘ toAngular := by
  funext y
  simp only [unit, if_neg hc, denominator_mask, if_false, Function.comp_apply,
    actualPair_face _ (radius_toAngular y)]
  cases v <;> rfl

/-- No angular or normalization derivative is discarded: the two retained
pair forms give exactly the genuine extended edge restricted to radius zero. -/
theorem edgeForm_eq_extended (ha : a ∈ S) (hb : b ∈ S) (hanchor : i ∈ S → a = i)
    (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j)
    (y : ProductCoordinates i a b S m) (hy : (toAngular y).toFree.OpenConditions) :
    edgeForm j v hv y =
      (extendedEdgeForm j v (toAngular y)).compContinuousLinearMap (fderiv ℝ toAngular y) := by
  unfold edgeForm pairForm
  rw [← angularPullback_div _ _ y ((contDiff_unit _).contDiffAt.differentiableAt (by simp))
    ((contDiff_unit _).contDiffAt.differentiableAt (by simp))
    (unit_ne_zero ha hb hanchor y hy _) (unit_ne_zero ha hb hanchor y hy _)]
  have hActual (v : Fin n ⊕ Fin m) : ContDiffAt ℝ ⊤
      (fun q : ClusterAngularCoordinates i a b S m ↦ harmonicRatio (actualPair j v q).1 (actualPair j v q).2)
      (toAngular y) := by
    have hp := contDiffAt_harmonicRatio (actualPair j v (toAngular y)).1 (actualPair j v (toAngular y)).2
      (actualPair_denominator_ne_zero _ hy (by simp) j v)
    exact hp.comp (toAngular y) (contDiff_actualPair j v).contDiffAt
  cases v with
  | inl k =>
    by_cases h : j ∈ S ∧ k ∈ S
    · rw [ratio_internal j k hv h.1 h.2, extendedEdgeForm, if_pos h]
      apply angularPullback_comp_differentiable
      · exact (((contDiffAt_variableInternalClusterRegularizedRatio _
          (internalDenominator_face_ne_zero _ hy (radius_toAngular y) j k)).comp _
          (contDiff_internalParameters j k).contDiffAt).differentiableAt (by simp))
      · exact contDiff_toAngular.contDiffAt.differentiableAt (by simp)
    · rw [ratio_external j (Sum.inl k) hv (by simpa only [numerator_internal_mask] using h),
        extendedEdgeForm, if_neg h]
      exact angularPullback_comp_differentiable _ _ y
        ((hActual (Sum.inl k)).differentiableAt (by simp))
        (contDiff_toAngular.contDiffAt.differentiableAt (by simp))
  | inr k =>
    rw [ratio_external j (Sum.inr k) hv (numerator_boundary_mask j k hv)]
    exact angularPullback_comp_differentiable _ _ y
      ((hActual (Sum.inr k)).differentiableAt (by simp))
      (contDiff_toAngular.contDiffAt.differentiableAt (by simp))

end EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFaceEdgeForms
