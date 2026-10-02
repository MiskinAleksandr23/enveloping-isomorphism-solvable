import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryAnchoredInfinityFreeCoordinateEquiv
import EnvelopingIsomorphism.Deformation.Kontsevich.RealClusterForms
import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterSmoothForms

/-! Smooth continuation of the actual harmonic edge forms in the free infinity coordinates. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration ComplexConjugate Topology

namespace BoundaryAnchoredInfinityFreeCoordinates

variable {n m : ℕ} {a : Fin n} {l u : Fin (m + 1)} {o : Fin m}

def targetShape (l u : Fin (m + 1)) (x : BoundaryAnchoredInfinityFreeCoordinates a m o) :
    Fin n ⊕ Fin m → ℂ
  | Sum.inl j => x.shape j
  | Sum.inr j => x.boundaryVelocity l u j

def position (l u : Fin (m + 1)) (x : BoundaryAnchoredInfinityFreeCoordinates a m o) :
    Fin n ⊕ Fin m → ℂ
  | Sum.inl j => x.scaledInterior j
  | Sum.inr j => x.scaledBoundary l u j

@[fun_prop] theorem contDiff_targetShape (l u : Fin (m + 1)) (v : Fin n ⊕ Fin m) :
    ContDiff ℝ ⊤ (fun x : BoundaryAnchoredInfinityFreeCoordinates a m o => x.targetShape l u v) := by
  cases v with
  | inl j => exact contDiff_shape j
  | inr j => exact Complex.ofRealCLM.contDiff.comp (contDiff_boundaryVelocity l u j)

@[fun_prop] theorem contDiff_position (l u : Fin (m + 1)) (v : Fin n ⊕ Fin m) :
    ContDiff ℝ ⊤ (fun x : BoundaryAnchoredInfinityFreeCoordinates a m o => x.position l u v) := by
  cases v with
  | inl j => exact contDiff_scaledInterior j
  | inr j => exact Complex.ofRealCLM.contDiff.comp (contDiff_scaledBoundary l u j)

def actualPair (l u : Fin (m + 1)) (j : Fin n) (v : Fin n ⊕ Fin m)
    (x : BoundaryAnchoredInfinityFreeCoordinates a m o) : ℂ × ℂ :=
  (x.scaledInterior j, x.position l u v)

@[fun_prop] theorem contDiff_actualPair (l u : Fin (m + 1)) (j : Fin n) (v : Fin n ⊕ Fin m) :
    ContDiff ℝ ⊤ (actualPair (a := a) (o := o) l u j v) :=
  (contDiff_scaledInterior j).prodMk (contDiff_position l u v)

def actualEdgeForm (l u : Fin (m + 1)) (j : Fin n) (v : Fin n ⊕ Fin m) :
    BoundaryAnchoredInfinityFreeCoordinates a m o →
      BoundaryAnchoredInfinityFreeCoordinates a m o [⋀^Fin 1]→L[ℝ] ℝ :=
  angularPullback (fun x => harmonicRatio (actualPair l u j v x).1 (actualPair l u j v x).2)

def shapePair (l u : Fin (m + 1)) (j : Fin n) (v : Fin n ⊕ Fin m)
    (x : BoundaryAnchoredInfinityFreeCoordinates a m o) : ℂ × ℂ :=
  (x.shape j, x.targetShape l u v)

@[fun_prop] theorem contDiff_shapePair (l u : Fin (m + 1)) (j : Fin n) (v : Fin n ⊕ Fin m) :
    ContDiff ℝ ⊤ (shapePair (a := a) (o := o) l u j v) :=
  (contDiff_shape j).prodMk (contDiff_targetShape l u v)

def internalRatio (l u : Fin (m + 1)) (j : Fin n) (v : Fin n ⊕ Fin m)
    (x : BoundaryAnchoredInfinityFreeCoordinates a m o) : ℂ :=
  harmonicRatio (x.shape j) (x.targetShape l u v)

def internalEdgeForm (l u : Fin (m + 1)) (j : Fin n) (v : Fin n ⊕ Fin m) :
    BoundaryAnchoredInfinityFreeCoordinates a m o →
      BoundaryAnchoredInfinityFreeCoordinates a m o [⋀^Fin 1]→L[ℝ] ℝ :=
  angularPullback (internalRatio l u j v)

theorem position_internal (x : BoundaryAnchoredInfinityFreeCoordinates a m o)
    (v : Fin n ⊕ Fin m) (hv : boundaryAnchoredInfinityCollapses l u (Sum.inl v)) :
    x.position l u v = (x.radius : ℂ) * x.targetShape l u v := by
  cases v with
  | inl j => rfl
  | inr j =>
      change j ∈ boundaryClusterBlock l u at hv
      change ((x.boundaryBase l u j + x.radius * x.boundaryVelocity l u j : ℝ) : ℂ) = _
      have hb : x.boundaryBase l u j = 0 := by simp [boundaryBase, hv]
      rw [hb, zero_add, Complex.ofReal_mul]
      rfl

theorem harmonicRatio_actualPair_internal (x : BoundaryAnchoredInfinityFreeCoordinates a m o)
    (j : Fin n) (v : Fin n ⊕ Fin m)
    (hv : boundaryAnchoredInfinityCollapses l u (Sum.inl v)) (hr : x.radius ≠ 0) :
    harmonicRatio (actualPair l u j v x).1 (actualPair l u j v x).2 = internalRatio l u j v x := by
  have hpair : actualPair l u j v x =
      realClusterPair (0, (x.radius, (x.shape j, x.targetShape l u v))) := by
    simp only [actualPair, scaledInterior, position_internal x v hv,
      realClusterPair, Complex.ofReal_zero, zero_add]
  rw [hpair, harmonicRatio_realClusterPair _ hr]
  rfl

theorem internalEdgeForm_eq_actual (x : BoundaryAnchoredInfinityFreeCoordinates a m o)
    (j : Fin n) (v : Fin n ⊕ Fin m)
    (hv : boundaryAnchoredInfinityCollapses l u (Sum.inl v)) (hr : x.radius ≠ 0) :
    internalEdgeForm l u j v x = actualEdgeForm l u j v x := by
  have hne : ∀ᶠ y : BoundaryAnchoredInfinityFreeCoordinates a m o in nhds x, y.radius ≠ 0 :=
    (isOpen_ne_fun continuous_radius continuous_const).mem_nhds hr
  have heq : (fun y : BoundaryAnchoredInfinityFreeCoordinates a m o =>
      harmonicRatio (actualPair l u j v y).1 (actualPair l u j v y).2) =ᶠ[nhds x] internalRatio l u j v :=
    hne.mono fun y hy => harmonicRatio_actualPair_internal y j v hv hy
  exact (angularPullback_congr_eventually heq).symm

/-- The exterior-boundary harmonic ratio before cancellation, regular at radius zero. -/
def externalRatio (l u : Fin (m + 1)) (j : Fin n) (k : Fin m)
    (x : BoundaryAnchoredInfinityFreeCoordinates a m o) : ℂ :=
  ((x.boundaryBase l u k : ℂ) + (x.radius : ℂ) * ((x.boundaryVelocity l u k : ℂ) - x.shape j)) /
    ((x.boundaryBase l u k : ℂ) + (x.radius : ℂ) * ((x.boundaryVelocity l u k : ℂ) - conj (x.shape j)))

theorem externalRatio_eq_actualRatio (l u : Fin (m + 1)) (j : Fin n) (k : Fin m) :
    externalRatio (a := a) (o := o) l u j k =
      fun x => harmonicRatio (actualPair l u j (Sum.inr k) x).1 (actualPair l u j (Sum.inr k) x).2 := by
  funext x
  unfold externalRatio harmonicRatio actualPair position scaledInterior scaledBoundary
  push_cast
  simp only [map_mul, Complex.conj_ofReal]
  congr 1 <;> ring

def externalEdgeForm (l u : Fin (m + 1)) (j : Fin n) (k : Fin m) :
    BoundaryAnchoredInfinityFreeCoordinates a m o →
      BoundaryAnchoredInfinityFreeCoordinates a m o [⋀^Fin 1]→L[ℝ] ℝ :=
  angularPullback (externalRatio l u j k)

theorem externalEdgeForm_eq_actual (l u : Fin (m + 1)) (j : Fin n) (k : Fin m) :
    externalEdgeForm (a := a) (o := o) l u j k = actualEdgeForm l u j (Sum.inr k) := by
  rw [externalEdgeForm, externalRatio_eq_actualRatio]
  rfl

theorem externalRatio_zero (x : BoundaryAnchoredInfinityFreeCoordinates a m o)
    (hr : x.radius = 0) (j : Fin n) (k : Fin m) (hb : x.boundaryBase l u k ≠ 0) :
    externalRatio l u j k x = 1 := by
  simp only [externalRatio, hr, Complex.ofReal_zero, zero_mul, add_zero]
  exact div_self (Complex.ofReal_ne_zero.mpr hb)

abbrev FaceCoordinates {n : ℕ} (a : Fin n) (m : ℕ) (o : Fin m) :=
  (BoundaryAnchoredInfinityFreeInterior a → ℂ) × (BoundaryAnchoredInfinityFreeBoundary o → ℝ)

def faceEmbedding : FaceCoordinates a m o →L[ℝ] BoundaryAnchoredInfinityFreeCoordinates a m o :=
  (ContinuousLinearMap.fst ℝ _ _).prod ((ContinuousLinearMap.snd ℝ _ _).prod 0)

@[simp] theorem faceEmbedding_apply (x : FaceCoordinates a m o) : faceEmbedding x = (x.1, x.2, 0) := rfl

@[simp] theorem radius_faceEmbedding (x : FaceCoordinates a m o) : (faceEmbedding x).radius = 0 := rfl

theorem contDiffAt_externalRatio_zero (x : BoundaryAnchoredInfinityFreeCoordinates a m o)
    (hr : x.radius = 0) (j : Fin n) (k : Fin m) (hb : x.boundaryBase l u k ≠ 0) :
    ContDiffAt ℝ ⊤ (externalRatio l u j k) x := by
  rw [externalRatio_eq_actualRatio]
  change ContDiffAt ℝ ⊤ ((fun z : ℂ × ℂ => harmonicRatio z.1 z.2) ∘ actualPair l u j (Sum.inr k)) x
  have hd : (actualPair l u j (Sum.inr k) x).2 - conj (actualPair l u j (Sum.inr k) x).1 ≠ 0 := by
    simpa [actualPair, position, scaledInterior, scaledBoundary, hr] using Complex.ofReal_ne_zero.mpr hb
  exact (contDiffAt_harmonicRatio _ _ hd).comp x (contDiff_actualPair l u j (Sum.inr k)).contDiffAt

theorem contDiffAt_externalEdgeForm_zero (x : BoundaryAnchoredInfinityFreeCoordinates a m o)
    (hr : x.radius = 0) (j : Fin n) (k : Fin m) (hb : x.boundaryBase l u k ≠ 0) :
    ContDiffAt ℝ ⊤ (externalEdgeForm l u j k) x :=
  contDiffAt_angularPullback _ _ (contDiffAt_externalRatio_zero x hr j k hb)
    (by rw [externalRatio_zero x hr j k hb]; exact one_ne_zero)

theorem extDeriv_externalEdgeForm_zero (x : BoundaryAnchoredInfinityFreeCoordinates a m o)
    (hr : x.radius = 0) (j : Fin n) (k : Fin m) (hb : x.boundaryBase l u k ≠ 0) :
    extDeriv (externalEdgeForm l u j k) x = 0 :=
  extDeriv_angularPullback _ _ (contDiffAt_externalRatio_zero x hr j k hb)
    (by rw [externalRatio_zero x hr j k hb]; exact one_ne_zero)

/-- Restriction to the full radial face vanishes, retaining every free shape and coarse tangent. -/
theorem externalEdgeForm_face (y : FaceCoordinates a m o) (j : Fin n) (k : Fin m)
    (hb : (faceEmbedding y).boundaryBase l u k ≠ 0) :
    (externalEdgeForm l u j k (faceEmbedding y)).compContinuousLinearMap faceEmbedding = 0 := by
  rw [externalEdgeForm, angularPullback_comp_clm _ _ _
    ((contDiffAt_externalRatio_zero (faceEmbedding y) rfl j k hb).differentiableAt (by simp))]
  have hn : ∀ᶠ z : FaceCoordinates a m o in nhds y, (faceEmbedding z).boundaryBase l u k ≠ 0 :=
    (isOpen_ne_fun ((continuous_boundaryBase l u k).comp faceEmbedding.continuous) continuous_const).mem_nhds hb
  have heq : (externalRatio l u j k ∘ (faceEmbedding (a := a) (o := o))) =ᶠ[nhds y] fun _ => 1 :=
    hn.mono fun z hz => externalRatio_zero (faceEmbedding z) rfl j k hz
  rw [angularPullback_congr_eventually heq]
  ext v
  simp [angularPullback, angularForm_apply]

def extendedEdgeForm (l u : Fin (m + 1)) (j : Fin n) (v : Fin n ⊕ Fin m) :
    BoundaryAnchoredInfinityFreeCoordinates a m o →
      BoundaryAnchoredInfinityFreeCoordinates a m o [⋀^Fin 1]→L[ℝ] ℝ :=
  match v with
  | Sum.inl k => internalEdgeForm l u j (Sum.inl k)
  | Sum.inr k => if k ∈ boundaryClusterBlock l u then internalEdgeForm l u j (Sum.inr k)
      else externalEdgeForm l u j k

theorem extendedEdgeForm_eq_actual (x : BoundaryAnchoredInfinityFreeCoordinates a m o)
    (j : Fin n) (v : Fin n ⊕ Fin m) (hr : x.radius ≠ 0) :
    extendedEdgeForm l u j v x = actualEdgeForm l u j v x := by
  cases v with
  | inl k => exact internalEdgeForm_eq_actual x j (Sum.inl k) True.intro hr
  | inr k =>
      by_cases hk : k ∈ boundaryClusterBlock l u
      · rw [extendedEdgeForm, if_pos hk]
        exact internalEdgeForm_eq_actual x j (Sum.inr k) hk hr
      · rw [extendedEdgeForm, if_neg hk, externalEdgeForm_eq_actual]

def shapeFacePair (l u : Fin (m + 1)) (j : Fin n) (v : Fin n ⊕ Fin m) :
    FaceCoordinates a m o → ℂ × ℂ := shapePair l u j v ∘ faceEmbedding

def shapeFaceForm (l u : Fin (m + 1)) (j : Fin n) (v : Fin n ⊕ Fin m)
    (y : FaceCoordinates a m o) : FaceCoordinates a m o [⋀^Fin 1]→L[ℝ] ℝ :=
  (harmonicAngleForm (shapeFacePair l u j v y)).compContinuousLinearMap
    (fderiv ℝ (shapeFacePair l u j v) y)

end BoundaryAnchoredInfinityFreeCoordinates

namespace BoundaryAnchoredInfinityFreeDomain

variable {n m : ℕ} {a : Fin n} {l u : Fin (m + 1)} {o : Fin m}

theorem shape_im_pos (x : BoundaryAnchoredInfinityFreeDomain a m l u o) (j : Fin n) :
    0 < (x.val.shape j).im := by
  rw [← x.datum_shape]
  exact (x.datum.shape j).im_pos

theorem targetShape_im_nonneg (x : BoundaryAnchoredInfinityFreeDomain a m l u o) (v : Fin n ⊕ Fin m) :
    0 ≤ (x.val.targetShape l u v).im := by
  cases v with
  | inl j => exact (x.shape_im_pos j).le
  | inr k => exact le_rfl

theorem shape_denominator_ne_zero (x : BoundaryAnchoredInfinityFreeDomain a m l u o)
    (j : Fin n) (v : Fin n ⊕ Fin m) :
    x.val.targetShape l u v - conj (x.val.shape j) ≠ 0 :=
  harmonicDenominator_ne_zero (x.shape_im_pos j) (x.targetShape_im_nonneg v)

theorem shape_numerator_ne_zero (x : BoundaryAnchoredInfinityFreeDomain a m l u o)
    (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j) :
    x.val.targetShape l u v - x.val.shape j ≠ 0 := by
  intro h
  have heq := sub_eq_zero.mp h
  cases v with
  | inl k =>
      apply hv
      apply congrArg Sum.inl
      apply x.datum.shape_injective
      apply UpperHalfPlane.ext
      simpa only [datum_shape, BoundaryAnchoredInfinityFreeCoordinates.targetShape] using heq
  | inr k =>
      have hi := congrArg Complex.im heq
      change 0 = (x.val.shape j).im at hi
      exact (x.shape_im_pos j).ne' hi.symm

theorem contDiffAt_internalRatio (x : BoundaryAnchoredInfinityFreeDomain a m l u o)
    (j : Fin n) (v : Fin n ⊕ Fin m) :
    ContDiffAt ℝ ⊤ (BoundaryAnchoredInfinityFreeCoordinates.internalRatio l u j v) x.val := by
  change ContDiffAt ℝ ⊤ ((fun z : ℂ × ℂ => harmonicRatio z.1 z.2) ∘
    BoundaryAnchoredInfinityFreeCoordinates.shapePair l u j v) x.val
  exact (contDiffAt_harmonicRatio _ _ (x.shape_denominator_ne_zero j v)).comp x.val
    (BoundaryAnchoredInfinityFreeCoordinates.contDiff_shapePair l u j v).contDiffAt

theorem internalRatio_ne_zero (x : BoundaryAnchoredInfinityFreeDomain a m l u o)
    (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j) :
    BoundaryAnchoredInfinityFreeCoordinates.internalRatio l u j v x.val ≠ 0 :=
  div_ne_zero (x.shape_numerator_ne_zero j v hv) (x.shape_denominator_ne_zero j v)

theorem contDiffAt_internalEdgeForm (x : BoundaryAnchoredInfinityFreeDomain a m l u o)
    (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j) :
    ContDiffAt ℝ ⊤ (BoundaryAnchoredInfinityFreeCoordinates.internalEdgeForm l u j v) x.val :=
  contDiffAt_angularPullback _ _ (x.contDiffAt_internalRatio j v) (x.internalRatio_ne_zero j v hv)

theorem outside_boundaryBase_ne_zero (x : BoundaryAnchoredInfinityFreeDomain a m l u o)
    (k : Fin m) (hk : k ∉ boundaryClusterBlock l u) : x.val.boundaryBase l u k ≠ 0 := by
  rw [← x.datum_boundaryBase]
  exact fun h => hk ((x.datum.boundaryBase_eq_zero_iff k).mp h)

theorem contDiffAt_externalEdgeForm_face (x : BoundaryAnchoredInfinityFreeDomain a m l u o)
    (hr : x.val.radius = 0) (j : Fin n) (k : Fin m) (hk : k ∉ boundaryClusterBlock l u) :
    ContDiffAt ℝ ⊤ (BoundaryAnchoredInfinityFreeCoordinates.externalEdgeForm l u j k) x.val :=
  BoundaryAnchoredInfinityFreeCoordinates.contDiffAt_externalEdgeForm_zero x.val hr j k
    (x.outside_boundaryBase_ne_zero k hk)

theorem contDiffAt_extendedEdgeForm_face (x : BoundaryAnchoredInfinityFreeDomain a m l u o)
    (hr : x.val.radius = 0) (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j) :
    ContDiffAt ℝ ⊤ (BoundaryAnchoredInfinityFreeCoordinates.extendedEdgeForm l u j v) x.val := by
  cases v with
  | inl k => exact x.contDiffAt_internalEdgeForm j (Sum.inl k) hv
  | inr k =>
      by_cases hk : k ∈ boundaryClusterBlock l u
      · rw [BoundaryAnchoredInfinityFreeCoordinates.extendedEdgeForm, if_pos hk]
        exact x.contDiffAt_internalEdgeForm j (Sum.inr k) hv
      · rw [BoundaryAnchoredInfinityFreeCoordinates.extendedEdgeForm, if_neg hk]
        exact x.contDiffAt_externalEdgeForm_face hr j k hk

theorem actualPair_denominator_ne_zero (x : BoundaryAnchoredInfinityFreeDomain a m l u o)
    (hr : 0 < x.val.radius) (j : Fin n) (v : Fin n ⊕ Fin m) :
    (BoundaryAnchoredInfinityFreeCoordinates.actualPair l u j v x.val).2 -
      conj (BoundaryAnchoredInfinityFreeCoordinates.actualPair l u j v x.val).1 ≠ 0 := by
  have hpos (k : Fin n) : 0 < (x.val.scaledInterior k).im := by
    simpa [BoundaryAnchoredInfinityFreeCoordinates.scaledInterior] using mul_pos hr (x.shape_im_pos k)
  apply harmonicDenominator_ne_zero (hpos j)
  cases v with
  | inl k => exact (hpos k).le
  | inr k => exact le_rfl

/-- At positive scale the extension is the actual full harmonic pullback along the actual point-pair map. -/
theorem extendedEdgeForm_eq_pullback (x : BoundaryAnchoredInfinityFreeDomain a m l u o)
    (hr : 0 < x.val.radius) (j : Fin n) (v : Fin n ⊕ Fin m) :
    BoundaryAnchoredInfinityFreeCoordinates.extendedEdgeForm l u j v x.val =
      (harmonicAngleForm (BoundaryAnchoredInfinityFreeCoordinates.actualPair l u j v x.val)).compContinuousLinearMap
        (fderiv ℝ (BoundaryAnchoredInfinityFreeCoordinates.actualPair l u j v) x.val) := by
  rw [BoundaryAnchoredInfinityFreeCoordinates.extendedEdgeForm_eq_actual x.val j v hr.ne']
  exact (harmonicAngleForm_pullback _ _
    ((BoundaryAnchoredInfinityFreeCoordinates.contDiff_actualPair l u j v).contDiffAt.differentiableAt (by simp))
    (x.actualPair_denominator_ne_zero hr j v)).symm

end BoundaryAnchoredInfinityFreeDomain

namespace BoundaryAnchoredInfinityFreeCoordinates

variable {n m : ℕ} {a : Fin n} {l u : Fin (m + 1)} {o : Fin m}

def faceDomain (y : FaceCoordinates a m o) (hy : (faceEmbedding y).OpenConditions l u) :
    BoundaryAnchoredInfinityFreeDomain a m l u o := ⟨faceEmbedding y, le_rfl, hy⟩

/-- Internal forms restrict to the full inner-shape harmonic form on all face coordinates. -/
theorem internalEdgeForm_face (y : FaceCoordinates a m o)
    (hy : (faceEmbedding y).OpenConditions l u) (j : Fin n) (v : Fin n ⊕ Fin m) :
    (internalEdgeForm l u j v (faceEmbedding y)).compContinuousLinearMap faceEmbedding =
      shapeFaceForm l u j v y := by
  let x := faceDomain y hy
  rw [internalEdgeForm, angularPullback_comp_clm _ _ _
    ((x.contDiffAt_internalRatio j v).differentiableAt (by simp))]
  exact (harmonicAngleForm_pullback _ _
    (((contDiff_shapePair l u j v).comp faceEmbedding.contDiff).contDiffAt.differentiableAt (by simp))
    (x.shape_denominator_ne_zero j v)).symm

theorem extendedEdgeForm_face_internal (y : FaceCoordinates a m o)
    (hy : (faceEmbedding y).OpenConditions l u) (j : Fin n) (v : Fin n ⊕ Fin m)
    (hv : boundaryAnchoredInfinityCollapses l u (Sum.inl v)) :
    (extendedEdgeForm l u j v (faceEmbedding y)).compContinuousLinearMap faceEmbedding =
      shapeFaceForm l u j v y := by
  cases v with
  | inl k => exact internalEdgeForm_face y hy j (Sum.inl k)
  | inr k =>
      change k ∈ boundaryClusterBlock l u at hv
      rw [extendedEdgeForm, if_pos hv]
      exact internalEdgeForm_face y hy j (Sum.inr k)

theorem extendedEdgeForm_face_outside (y : FaceCoordinates a m o)
    (hy : (faceEmbedding y).OpenConditions l u) (j : Fin n) (k : Fin m)
    (hk : k ∉ boundaryClusterBlock l u) :
    (extendedEdgeForm l u j (Sum.inr k) (faceEmbedding y)).compContinuousLinearMap faceEmbedding = 0 := by
  rw [extendedEdgeForm, if_neg hk]
  exact externalEdgeForm_face y j k ((faceDomain y hy).outside_boundaryBase_ne_zero k hk)

end BoundaryAnchoredInfinityFreeCoordinates

end EnvelopingIsomorphism.Deformation.Kontsevich
