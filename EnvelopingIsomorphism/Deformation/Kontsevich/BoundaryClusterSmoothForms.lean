import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterFreeChart
import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterSmoothForms
import EnvelopingIsomorphism.Deformation.Kontsevich.RealClusterExternalForms

/-! Actual harmonic edge forms in free finite real-cluster coordinates.
Internal edges retain the shape harmonic ratio; all other edges retain their
ordinary harmonic ratio. These are smooth closed forms through the face and
agree with actual harmonic pullbacks at positive admissible radius. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration ComplexConjugate Topology

namespace BoundaryClusterFreeCoordinates

variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

def targetBase (l u : Fin (m + 1)) (x : BoundaryClusterFreeCoordinates i a S m) : Fin n ⊕ Fin m → ℂ
  | Sum.inl j => x.base j
  | Sum.inr j => (x.boundaryBase l u j : ℂ)

def targetVelocity (l u : Fin (m + 1)) (x : BoundaryClusterFreeCoordinates i a S m) : Fin n ⊕ Fin m → ℂ
  | Sum.inl j => x.velocity j
  | Sum.inr j => (x.boundaryVelocity l u j : ℂ)

def position (l u : Fin (m + 1)) (x : BoundaryClusterFreeCoordinates i a S m) (v : Fin n ⊕ Fin m) : ℂ :=
  x.targetBase l u v + (x.radius : ℂ) * x.targetVelocity l u v

@[fun_prop] theorem contDiff_targetBase (l u : Fin (m + 1)) (v : Fin n ⊕ Fin m) :
    ContDiff ℝ ⊤ (fun x : BoundaryClusterFreeCoordinates i a S m => x.targetBase l u v) := by
  cases v with
  | inl j => exact contDiff_base j
  | inr j => exact Complex.ofRealCLM.contDiff.comp (contDiff_boundaryBase l u j)

@[fun_prop] theorem contDiff_targetVelocity (l u : Fin (m + 1)) (v : Fin n ⊕ Fin m) :
    ContDiff ℝ ⊤ (fun x : BoundaryClusterFreeCoordinates i a S m => x.targetVelocity l u v) := by
  cases v with
  | inl j => exact contDiff_velocity j
  | inr j => exact Complex.ofRealCLM.contDiff.comp (contDiff_boundaryVelocity l u j)

@[fun_prop] theorem contDiff_position (l u : Fin (m + 1)) (v : Fin n ⊕ Fin m) :
    ContDiff ℝ ⊤ (fun x : BoundaryClusterFreeCoordinates i a S m => x.position l u v) :=
  (contDiff_targetBase l u v).add
    ((Complex.ofRealCLM.contDiff.comp contDiff_radius).mul (contDiff_targetVelocity l u v))

def actualPair (l u : Fin (m + 1)) (j : Fin n) (v : Fin n ⊕ Fin m)
    (x : BoundaryClusterFreeCoordinates i a S m) : ℂ × ℂ :=
  (x.position l u (Sum.inl j), x.position l u v)

@[fun_prop] theorem contDiff_actualPair (l u : Fin (m + 1)) (j : Fin n) (v : Fin n ⊕ Fin m) :
    ContDiff ℝ ⊤ (actualPair (i := i) (a := a) (S := S) l u j v) :=
  (contDiff_position l u (Sum.inl j)).prodMk (contDiff_position l u v)

def actualEdgeForm (l u : Fin (m + 1)) (j : Fin n) (v : Fin n ⊕ Fin m)
    (x : BoundaryClusterFreeCoordinates i a S m) :
    BoundaryClusterFreeCoordinates i a S m [⋀^Fin 1]→L[ℝ] ℝ :=
  angularPullback (fun y => harmonicRatio (actualPair l u j v y).1 (actualPair l u j v y).2) x

def shapePair (l u : Fin (m + 1)) (j : Fin n) (v : Fin n ⊕ Fin m)
    (x : BoundaryClusterFreeCoordinates i a S m) : ℂ × ℂ :=
  (x.velocity j, x.targetVelocity l u v)

@[fun_prop] theorem contDiff_shapePair (l u : Fin (m + 1)) (j : Fin n) (v : Fin n ⊕ Fin m) :
    ContDiff ℝ ⊤ (shapePair (i := i) (a := a) (S := S) l u j v) :=
  (contDiff_velocity j).prodMk (contDiff_targetVelocity l u v)

def internalRatio (l u : Fin (m + 1)) (j : Fin n) (v : Fin n ⊕ Fin m)
    (x : BoundaryClusterFreeCoordinates i a S m) : ℂ :=
  harmonicRatio (x.velocity j) (x.targetVelocity l u v)

def internalEdgeForm (l u : Fin (m + 1)) (j : Fin n) (v : Fin n ⊕ Fin m)
    (x : BoundaryClusterFreeCoordinates i a S m) :
    BoundaryClusterFreeCoordinates i a S m [⋀^Fin 1]→L[ℝ] ℝ :=
  angularPullback (internalRatio l u j v) x

theorem targetBase_eq_center (x : BoundaryClusterFreeCoordinates i a S m) (v : Fin n ⊕ Fin m)
    (hv : boundaryClusterCollapses S l u (Sum.inl v)) : x.targetBase l u v = (x.center : ℂ) := by
  cases v with
  | inl j => exact x.base_eq_center j hv
  | inr j => exact congrArg Complex.ofReal (x.boundaryBase_eq_center l u j hv)

theorem harmonicRatio_actualPair_internal (x : BoundaryClusterFreeCoordinates i a S m)
    (j : Fin n) (v : Fin n ⊕ Fin m) (hj : j ∈ S)
    (hv : boundaryClusterCollapses S l u (Sum.inl v)) (hr : x.radius ≠ 0) :
    harmonicRatio (actualPair l u j v x).1 (actualPair l u j v x).2 = internalRatio l u j v x := by
  have hpair : actualPair l u j v x =
      realClusterPair (x.center, (x.radius, (x.velocity j, x.targetVelocity l u v))) := by
    change (x.base j + (x.radius : ℂ) * x.velocity j,
      x.targetBase l u v + (x.radius : ℂ) * x.targetVelocity l u v) =
      ((x.center : ℂ) + (x.radius : ℂ) * x.velocity j,
        (x.center : ℂ) + (x.radius : ℂ) * x.targetVelocity l u v)
    rw [x.base_eq_center j hj, x.targetBase_eq_center v hv]
  rw [hpair, harmonicRatio_realClusterPair _ hr]
  rfl

/-- At nonzero scale, radial and translation cancellation identifies the complete pullback. -/
theorem internalEdgeForm_eq_actual (x : BoundaryClusterFreeCoordinates i a S m)
    (j : Fin n) (v : Fin n ⊕ Fin m) (hj : j ∈ S)
    (hv : boundaryClusterCollapses S l u (Sum.inl v)) (hr : x.radius ≠ 0) :
    internalEdgeForm l u j v x = actualEdgeForm l u j v x := by
  have hne : ∀ᶠ y : BoundaryClusterFreeCoordinates i a S m in nhds x, y.radius ≠ 0 :=
    (isOpen_ne_fun continuous_radius continuous_const).mem_nhds hr
  have heq : (fun y : BoundaryClusterFreeCoordinates i a S m =>
      harmonicRatio (actualPair l u j v y).1 (actualPair l u j v y).2)
      =ᶠ[nhds x] internalRatio l u j v :=
    hne.mono fun y hy => harmonicRatio_actualPair_internal y j v hj hv hy
  exact (angularPullback_congr_eventually heq).symm

theorem actualPair_face (x : BoundaryClusterFreeCoordinates i a S m) (hr : x.radius = 0)
    (j : Fin n) (v : Fin n ⊕ Fin m) : actualPair l u j v x = (x.base j, x.targetBase l u v) := by
  simp only [actualPair, position, hr, Complex.ofReal_zero, zero_mul, add_zero, targetBase]

def extendedEdgeForm (l u : Fin (m + 1)) (j : Fin n) (v : Fin n ⊕ Fin m) :
    BoundaryClusterFreeCoordinates i a S m → BoundaryClusterFreeCoordinates i a S m [⋀^Fin 1]→L[ℝ] ℝ :=
  if j ∈ S ∧ boundaryClusterCollapses S l u (Sum.inl v) then internalEdgeForm l u j v
  else actualEdgeForm l u j v

theorem extendedEdgeForm_eq_actual (x : BoundaryClusterFreeCoordinates i a S m)
    (j : Fin n) (v : Fin n ⊕ Fin m) (hr : x.radius ≠ 0) :
    extendedEdgeForm l u j v x = actualEdgeForm l u j v x := by
  by_cases h : j ∈ S ∧ boundaryClusterCollapses S l u (Sum.inl v)
  · rw [extendedEdgeForm, if_pos h]
    exact internalEdgeForm_eq_actual x j v h.1 h.2 hr
  · rw [extendedEdgeForm, if_neg h]

end BoundaryClusterFreeCoordinates

namespace BoundaryClusterFreeDomain

variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

@[simp] theorem datum_targetBase (x : BoundaryClusterFreeDomain i a S m l u) (v : Fin n ⊕ Fin m) :
    x.datum.baseVertex v = x.val.targetBase l u v := by
  cases v with
  | inl j => exact x.datum_base j
  | inr j => exact congrArg Complex.ofReal (x.datum_boundaryBase j)

@[simp] theorem datum_targetVelocity (x : BoundaryClusterFreeDomain i a S m l u) (v : Fin n ⊕ Fin m) :
    x.datum.velocityVertex v = x.val.targetVelocity l u v := by
  cases v with
  | inl j => exact x.datum_velocity j
  | inr j => exact congrArg Complex.ofReal (x.datum_boundaryVelocity j)

theorem position_im_pos (x : BoundaryClusterFreeDomain i a S m l u) (hr : 0 < x.val.radius) (j : Fin n) :
    0 < (x.val.position l u (Sum.inl j)).im := by
  change 0 < (x.val.base j + (x.val.radius : ℂ) * x.val.velocity j).im
  simpa only [BoundaryClusterData.scaledInterior, datum_base, datum_velocity] using
    x.datum.scaledInterior_im_pos hr j

theorem actualPair_denominator_ne_zero (x : BoundaryClusterFreeDomain i a S m l u)
    (hr : 0 < x.val.radius) (j : Fin n) (v : Fin n ⊕ Fin m) :
    (BoundaryClusterFreeCoordinates.actualPair l u j v x.val).2 -
      conj (BoundaryClusterFreeCoordinates.actualPair l u j v x.val).1 ≠ 0 := by
  apply harmonicDenominator_ne_zero (x.position_im_pos hr j)
  cases v with
  | inl k => exact (x.position_im_pos hr k).le
  | inr k =>
    simp [BoundaryClusterFreeCoordinates.actualPair, BoundaryClusterFreeCoordinates.position,
      BoundaryClusterFreeCoordinates.targetBase, BoundaryClusterFreeCoordinates.targetVelocity]

theorem actualEdgeForm_eq_pullback (x : BoundaryClusterFreeDomain i a S m l u)
    (hr : 0 < x.val.radius) (j : Fin n) (v : Fin n ⊕ Fin m) :
    BoundaryClusterFreeCoordinates.actualEdgeForm l u j v x.val =
      (harmonicAngleForm (BoundaryClusterFreeCoordinates.actualPair l u j v x.val)).compContinuousLinearMap
        (fderiv ℝ (BoundaryClusterFreeCoordinates.actualPair l u j v) x.val) :=
  (harmonicAngleForm_pullback _ _
    ((BoundaryClusterFreeCoordinates.contDiff_actualPair l u j v).contDiffAt.differentiableAt (by simp))
    (x.actualPair_denominator_ne_zero hr j v)).symm

theorem shape_numerator_ne_zero (x : BoundaryClusterFreeDomain i a S m l u)
    (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j) (hj : j ∈ S)
    (hc : boundaryClusterCollapses S l u (Sum.inl v)) :
    x.val.targetVelocity l u v - x.val.velocity j ≠ 0 := by
  have hp : boundaryClusterPairCollapses S l u (harmonicNumeratorPair j v hv) := ⟨hj, hc⟩
  have h := x.datum.pairVelocity_ne_zero_of_boundaryClusterPairCollapses (harmonicNumeratorPair j v hv) hp
  change x.datum.velocityVertex v - x.datum.velocity j ≠ 0 at h
  simpa only [datum_targetVelocity, datum_velocity] using h

theorem shape_denominator_ne_zero (x : BoundaryClusterFreeDomain i a S m l u)
    (j : Fin n) (v : Fin n ⊕ Fin m) (hj : j ∈ S) :
    x.val.targetVelocity l u v - conj (x.val.velocity j) ≠ 0 := by
  have h := harmonicDenominator_ne_zero (x.datum.velocity_im_pos j hj) (x.datum.velocityVertex_im_nonneg v)
  simpa only [datum_targetVelocity, datum_velocity] using h

theorem contDiffAt_internalRatio (x : BoundaryClusterFreeDomain i a S m l u)
    (j : Fin n) (v : Fin n ⊕ Fin m) (hj : j ∈ S) :
    ContDiffAt ℝ ⊤ (BoundaryClusterFreeCoordinates.internalRatio l u j v) x.val := by
  change ContDiffAt ℝ ⊤ ((fun z : ℂ × ℂ => harmonicRatio z.1 z.2) ∘
    BoundaryClusterFreeCoordinates.shapePair l u j v) x.val
  exact (contDiffAt_harmonicRatio _ _ (x.shape_denominator_ne_zero j v hj)).comp x.val
    (BoundaryClusterFreeCoordinates.contDiff_shapePair l u j v).contDiffAt

theorem internalRatio_ne_zero (x : BoundaryClusterFreeDomain i a S m l u)
    (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j) (hj : j ∈ S)
    (hc : boundaryClusterCollapses S l u (Sum.inl v)) :
    BoundaryClusterFreeCoordinates.internalRatio l u j v x.val ≠ 0 :=
  div_ne_zero (x.shape_numerator_ne_zero j v hv hj hc) (x.shape_denominator_ne_zero j v hj)

theorem external_base_ne (x : BoundaryClusterFreeDomain i a S m l u)
    (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j)
    (hc : ¬(j ∈ S ∧ boundaryClusterCollapses S l u (Sum.inl v))) :
    x.val.targetBase l u v ≠ x.val.base j := by
  have hmask : ¬boundaryClusterPairCollapses S l u (harmonicNumeratorPair j v hv) := hc
  have hpair : x.datum.pairBase (harmonicNumeratorPair j v hv) ≠ 0 :=
    fun h => hmask ((x.datum.pairBase_eq_zero_iff_boundaryClusterPairCollapses _).mp h)
  change x.datum.baseVertex v - x.datum.base j ≠ 0 at hpair
  simpa only [datum_targetBase, datum_base] using sub_ne_zero.mp hpair

theorem external_denominator_ne_zero (x : BoundaryClusterFreeDomain i a S m l u)
    (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j)
    (hc : ¬(j ∈ S ∧ boundaryClusterCollapses S l u (Sum.inl v))) :
    x.val.targetBase l u v - conj (x.val.base j) ≠ 0 := by
  have hb : x.datum.baseVertex v ≠ x.datum.base j := by
    simpa only [datum_targetBase, datum_base] using x.external_base_ne j v hv hc
  simpa only [datum_targetBase, datum_base] using x.datum.base_harmonicDenominator_ne_zero j v hb

theorem contDiffAt_externalRatio_face (x : BoundaryClusterFreeDomain i a S m l u)
    (hr : x.val.radius = 0) (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j)
    (hc : ¬(j ∈ S ∧ boundaryClusterCollapses S l u (Sum.inl v))) :
    ContDiffAt ℝ ⊤ (fun y => harmonicRatio (BoundaryClusterFreeCoordinates.actualPair l u j v y).1
      (BoundaryClusterFreeCoordinates.actualPair l u j v y).2) x.val := by
  have hd := x.external_denominator_ne_zero j v hv hc
  apply (contDiffAt_harmonicRatio _ _ ?_).comp x.val
    (BoundaryClusterFreeCoordinates.contDiff_actualPair l u j v).contDiffAt
  change (BoundaryClusterFreeCoordinates.actualPair l u j v x.val).2 -
    conj (BoundaryClusterFreeCoordinates.actualPair l u j v x.val).1 ≠ 0
  rw [BoundaryClusterFreeCoordinates.actualPair_face x.val hr]
  exact hd

theorem externalRatio_face_ne_zero (x : BoundaryClusterFreeDomain i a S m l u)
    (hr : x.val.radius = 0) (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j)
    (hc : ¬(j ∈ S ∧ boundaryClusterCollapses S l u (Sum.inl v))) :
    harmonicRatio (BoundaryClusterFreeCoordinates.actualPair l u j v x.val).1
      (BoundaryClusterFreeCoordinates.actualPair l u j v x.val).2 ≠ 0 := by
  rw [BoundaryClusterFreeCoordinates.actualPair_face x.val hr]
  exact div_ne_zero (sub_ne_zero.mpr (x.external_base_ne j v hv hc)) (x.external_denominator_ne_zero j v hv hc)

/-- All nonloop edges have genuine smooth extensions in every free coordinate. -/
theorem contDiffAt_extendedEdgeForm_face (x : BoundaryClusterFreeDomain i a S m l u)
    (hr : x.val.radius = 0) (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j) :
    ContDiffAt ℝ ⊤ (BoundaryClusterFreeCoordinates.extendedEdgeForm l u j v) x.val := by
  by_cases hc : j ∈ S ∧ boundaryClusterCollapses S l u (Sum.inl v)
  · rw [BoundaryClusterFreeCoordinates.extendedEdgeForm, if_pos hc]
    exact contDiffAt_angularPullback _ _ (x.contDiffAt_internalRatio j v hc.1) (x.internalRatio_ne_zero j v hv hc.1 hc.2)
  · rw [BoundaryClusterFreeCoordinates.extendedEdgeForm, if_neg hc]
    exact contDiffAt_angularPullback _ _ (x.contDiffAt_externalRatio_face hr j v hv hc)
      (x.externalRatio_face_ne_zero hr j v hv hc)

theorem extDeriv_extendedEdgeForm_face (x : BoundaryClusterFreeDomain i a S m l u)
    (hr : x.val.radius = 0) (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j) :
    extDeriv (BoundaryClusterFreeCoordinates.extendedEdgeForm l u j v) x.val = 0 := by
  by_cases hc : j ∈ S ∧ boundaryClusterCollapses S l u (Sum.inl v)
  · rw [BoundaryClusterFreeCoordinates.extendedEdgeForm, if_pos hc]
    exact extDeriv_angularPullback _ _ (x.contDiffAt_internalRatio j v hc.1) (x.internalRatio_ne_zero j v hv hc.1 hc.2)
  · rw [BoundaryClusterFreeCoordinates.extendedEdgeForm, if_neg hc]
    exact extDeriv_angularPullback _ _ (x.contDiffAt_externalRatio_face hr j v hv hc)
      (x.externalRatio_face_ne_zero hr j v hv hc)

/-- At positive admissible scale the smooth extension is exactly the original harmonic pullback. -/
theorem extendedEdgeForm_eq_pullback (x : BoundaryClusterFreeDomain i a S m l u)
    (hr : 0 < x.val.radius) (j : Fin n) (v : Fin n ⊕ Fin m) :
    BoundaryClusterFreeCoordinates.extendedEdgeForm l u j v x.val =
      (harmonicAngleForm (BoundaryClusterFreeCoordinates.actualPair l u j v x.val)).compContinuousLinearMap
        (fderiv ℝ (BoundaryClusterFreeCoordinates.actualPair l u j v) x.val) := by
  rw [BoundaryClusterFreeCoordinates.extendedEdgeForm_eq_actual x.val j v hr.ne']
  exact x.actualEdgeForm_eq_pullback hr j v

theorem toCompactification_position (x : BoundaryClusterFreeDomain i a S m l u) (v : Fin n ⊕ Fin m) :
    x.toCompactification.val.1 v = (x.val.position l u v : OnePoint ℂ) := by
  change ((x.datum.doubledBase (Sum.inl v) + (x.val.radius : ℂ) *
    x.datum.doubledVelocity (Sum.inl v) : ℂ) : OnePoint ℂ) = _
  change ((x.datum.baseVertex v + (x.val.radius : ℂ) * x.datum.velocityVertex v : ℂ) : OnePoint ℂ) = _
  rw [datum_targetBase, datum_targetVelocity]
  rfl

end BoundaryClusterFreeDomain

end EnvelopingIsomorphism.Deformation.Kontsevich
