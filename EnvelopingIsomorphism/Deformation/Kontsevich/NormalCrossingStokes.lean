import EnvelopingIsomorphism.Deformation.Kontsevich.PuncturedProductStokes

/-! Actual Stokes across simultaneous normal-crossing complex coordinate divisors.
The real/radial block precedes the imaginary/angular block throughout. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.NormalCrossingStokes

open Set MeasureTheory ContinuousAlternatingMap Filter
open BoxStokes
open scoped Topology

abbrev Degree (N : ℕ) := N + 1 + N
abbrev Dim (N : ℕ) := Degree N + 1
abbrev Space (N : ℕ) := Fin (N + 1) → ℂ
abbrev Cart (N : ℕ) := Fin (N + 1) → ℝ × ℝ
abbrev CrossingForm (N : ℕ) := Space N → Space N [⋀^Fin (Degree N)]→L[ℝ] ℝ

theorem degree_eq (N : ℕ) : Degree N = 2 * (N + 1) - 1 := by
  dsimp [Degree]
  omega

def radiusIndex {N : ℕ} (i : Fin (N + 1)) : Fin (Dim N) := i.castAdd (N + 1)
def angleIndex {N : ℕ} (i : Fin (N + 1)) : Fin (Dim N) := Fin.natAdd (N + 1) i

@[simp] theorem radiusIndex_val {N : ℕ} (i : Fin (N + 1)) : (radiusIndex i).val = i.val := rfl
@[simp] theorem angleIndex_val {N : ℕ} (i : Fin (N + 1)) : (angleIndex i).val = N + 1 + i.val := rfl

@[simp] theorem radiusIndex_inj {N : ℕ} (i j : Fin (N + 1)) : radiusIndex i = radiusIndex j ↔ i = j :=
  Fin.castAdd_inj
@[simp] theorem angleIndex_inj {N : ℕ} (i j : Fin (N + 1)) : angleIndex i = angleIndex j ↔ i = j :=
  Fin.natAdd_inj _
@[simp] theorem radiusIndex_ne_angleIndex {N : ℕ} (i j : Fin (N + 1)) : radiusIndex i ≠ angleIndex j := by
  intro h
  have hh := congrArg Fin.val h
  simp only [radiusIndex_val, angleIndex_val] at hh
  omega
@[simp] theorem angleIndex_ne_radiusIndex {N : ℕ} (i j : Fin (N + 1)) : angleIndex i ≠ radiusIndex j :=
  (radiusIndex_ne_angleIndex j i).symm

def split (N : ℕ) : Coord (Dim N) ≃L[ℝ] Cart N where
  toFun x i := (x (radiusIndex i), x (angleIndex i))
  invFun p := Fin.addCases (m := N + 1) (n := N + 1) (fun i ↦ (p i).1) (fun i ↦ (p i).2)
  left_inv x := by
    funext j
    refine Fin.addCases (m := N + 1) (n := N + 1) (fun i ↦ ?_) (fun i ↦ ?_) j <;> simp only [radiusIndex, angleIndex, Fin.addCases_left, Fin.addCases_right]
  right_inv p := by
    funext i
    simp only [radiusIndex, angleIndex, Fin.addCases_left, Fin.addCases_right, Prod.mk.eta]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply continuous_pi
    intro j
    refine Fin.addCases (m := N + 1) (n := N + 1) (fun i ↦ ?_) (fun i ↦ ?_) j <;> simp only [Fin.addCases_left, Fin.addCases_right] <;> fun_prop

@[simp] theorem split_apply {N : ℕ} (x : Coord (Dim N)) (i : Fin (N + 1)) :
    split N x i = (x (radiusIndex i), x (angleIndex i)) := rfl

def splitMeas (N : ℕ) : Coord (Dim N) ≃ᵐ Cart N :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin (Dim N) ↦ ℝ) (finSumFinEquiv (m := N + 1) (n := N + 1))).symm.trans
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin (N + 1) ⊕ Fin (N + 1) ↦ ℝ)).trans
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin (N + 1))).symm)

theorem splitMeas_apply (N : ℕ) (x : Coord (Dim N)) : splitMeas N x = split N x := rfl

theorem volume_preserving_split (N : ℕ) : MeasurePreserving (splitMeas N) :=
  ((volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin (N + 1))).symm _).comp
    ((volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin (N + 1) ⊕ Fin (N + 1) ↦ ℝ)).comp
      ((volume_measurePreserving_piCongrLeft (fun _ : Fin (Dim N) ↦ ℝ) (finSumFinEquiv (m := N + 1) (n := N + 1))).symm _))

def complexConvert (N : ℕ) : Cart N →L[ℝ] Space N :=
  ContinuousLinearMap.pi (fun i ↦ Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.proj i))

def frame (N : ℕ) : Fin (Dim N) → Space N :=
  (complexConvert N : Cart N → Space N) ∘ (split N : Coord (Dim N) → Cart N) ∘ standardBasis (Dim N)

def density {N : ℕ} (ω : CrossingForm N) (z : Space N) : ℝ := extDeriv ω z (frame N)

def coordinatePair {N : ℕ} (i : Fin (N + 1)) : Coord (Dim N) →L[ℝ] Coord 2 :=
  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.proj i).comp (split N).toContinuousLinearMap)

def polar {N : ℕ} (x : Coord (Dim N)) : Space N :=
  fun i ↦ PuncturedCoordinateStokes.polar (coordinatePair i x)

theorem polar_apply {N : ℕ} (x : Coord (Dim N)) (i : Fin (N + 1)) :
    polar x i = LogCircle.shrinkingCircle (x (radiusIndex i)) (x (angleIndex i)) := rfl

theorem polar_eq_native {N : ℕ} (x : Coord (Dim N)) :
    polar x = fun i ↦ Complex.polarCoord.symm (split N x i) :=
  funext (fun i ↦ PuncturedCoordinateStokes.polar_eq_native (coordinatePair i x))

@[fun_prop] theorem contDiff_polar (N : ℕ) : ContDiff ℝ ⊤ (@polar N) := by
  apply contDiff_pi.mpr
  intro i
  exact PuncturedCoordinateStokes.contDiff_polar.comp (coordinatePair i).contDiff

def polarDerivative {N : ℕ} (x : Coord (Dim N)) : Coord (Dim N) →L[ℝ] Space N :=
  ContinuousLinearMap.pi (fun i ↦ (PuncturedCoordinateStokes.polarDerivative (coordinatePair i x)).comp
    (coordinatePair i))

theorem hasFDerivAt_polar {N : ℕ} (x : Coord (Dim N)) : HasFDerivAt polar (polarDerivative x) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  exact (PuncturedCoordinateStokes.hasFDerivAt_polar _).comp x (coordinatePair i).hasFDerivAt

@[simp] theorem fderiv_polar {N : ℕ} (x : Coord (Dim N)) :
    fderiv ℝ polar x = polarDerivative x := (hasFDerivAt_polar x).fderiv

theorem polarDerivative_apply {N : ℕ} (x v : Coord (Dim N)) (i : Fin (N + 1)) :
    polarDerivative x v i = circleParameter (x (angleIndex i)) * (v (radiusIndex i) : ℂ) +
      (polar x i * Complex.I) * (v (angleIndex i) : ℂ) := by
  rfl

theorem polarDerivative_eq_native {N : ℕ} (x : Coord (Dim N)) :
    polarDerivative x = (complexConvert N).comp
      ((fderivPiPolarCoordSymm (split N x)).comp (split N).toContinuousLinearMap) := by
  have h := (complexConvert N).hasFDerivAt.comp x
    ((hasFDerivAt_pi_polarCoord_symm (split N x)).comp x (split N).hasFDerivAt)
  have heq : (fun y ↦ complexConvert N (fun i ↦ polarCoord.symm (split N y i))) = @polar N := by
    funext y
    exact (polar_eq_native y).symm
  change HasFDerivAt (fun y ↦ complexConvert N (fun i ↦ polarCoord.symm (split N y i))) _ x at h
  rw [heq] at h
  exact (hasFDerivAt_polar x).unique h

/-- The exact product of positive radial Jacobians in the fixed block-coordinate frame. -/
theorem topForm_polar_frame {N : ℕ} (α : Space N [⋀^Fin (Dim N)]→L[ℝ] ℝ) (x : Coord (Dim N)) :
    α ((polarDerivative x : Coord (Dim N) → Space N) ∘ standardBasis (Dim N)) =
      (∏ i : Fin (N + 1), x (radiusIndex i)) * α (frame N) := by
  let b := (Pi.basisFun ℝ (Fin (Dim N))).map (split N).toLinearEquiv
  let β := α.toAlternatingMap.compLinearMap (complexConvert N).toLinearMap
  have hb : (b : Fin (Dim N) → Cart N) = (split N : Coord (Dim N) → Cart N) ∘ standardBasis (Dim N) := by
    funext i
    simp [b, standardBasis, Pi.basisFun_apply]
  rw [polarDerivative_eq_native]
  change β ((fderivPiPolarCoordSymm (split N x) : Cart N → Cart N) ∘
    ((split N : Coord (Dim N) → Cart N) ∘ standardBasis (Dim N))) = _
  rw [← hb]
  have he := β.eq_smul_basis_det b
  have hh := congrArg (fun γ : Cart N [⋀^Fin (Dim N)]→ₗ[ℝ] ℝ ↦
    γ ((fderivPiPolarCoordSymm (split N x) : Cart N → Cart N) ∘ b)) he
  simp only [AlternatingMap.smul_apply, smul_eq_mul] at hh
  have hdet := b.det_comp (fderivPiPolarCoordSymm (split N x)).toLinearMap b
  simp only [ContinuousLinearMap.coe_coe, b.det_self, mul_one] at hdet
  rw [hdet] at hh
  rw [show LinearMap.det (fderivPiPolarCoordSymm (split N x)).toLinearMap =
    ∏ i, x (radiusIndex i) from det_fderivPiPolarCoordSymm (split N x)] at hh
  rw [hh, mul_comm]
  congr 1
  rw [hb]
  rfl

def lower (N : ℕ) (ε : ℝ) : Coord (Dim N) :=
  Fin.addCases (m := N + 1) (n := N + 1) (fun _ ↦ ε) (fun _ ↦ -Real.pi)
def upper (N : ℕ) (R : ℝ) : Coord (Dim N) :=
  Fin.addCases (m := N + 1) (n := N + 1) (fun _ ↦ R) (fun _ ↦ Real.pi)

@[simp] theorem lower_radius {N : ℕ} (ε : ℝ) (i : Fin (N + 1)) : lower N ε (radiusIndex i) = ε :=
  Fin.addCases_left i
@[simp] theorem lower_angle {N : ℕ} (ε : ℝ) (i : Fin (N + 1)) : lower N ε (angleIndex i) = -Real.pi :=
  Fin.addCases_right i
@[simp] theorem upper_radius {N : ℕ} (R : ℝ) (i : Fin (N + 1)) : upper N R (radiusIndex i) = R :=
  Fin.addCases_left i
@[simp] theorem upper_angle {N : ℕ} (R : ℝ) (i : Fin (N + 1)) : upper N R (angleIndex i) = Real.pi :=
  Fin.addCases_right i

def polarBox (N : ℕ) (ε R : ℝ) (h : ε < R) : BoxIntegral.Box (Fin (Dim N)) where
  lower := lower N ε
  upper := upper N R
  lower_lt_upper j := by
    refine Fin.addCases (m := N + 1) (n := N + 1) (fun i ↦ ?_) (fun i ↦ ?_) j
    · simpa only [lower, upper, Fin.addCases_left] using h
    · simp only [lower, upper, Fin.addCases_right]
      linarith [Real.pi_pos]

def multiAnnulus (N : ℕ) (ε R : ℝ) : Set (Space N) :=
  univ.pi (fun _ ↦ PolarAnnulus.annulus ε R)
def polarRectangle (N : ℕ) (ε R : ℝ) : Set (Cart N) :=
  univ.pi (fun _ ↦ PolarAnnulus.rectangle ε R)
def finRectangle (N : ℕ) (ε R : ℝ) : Set (Coord (Dim N)) :=
  univ.pi (fun j ↦ Ioo (lower N ε j) (upper N R j))

theorem measurableSet_multiAnnulus (N : ℕ) (ε R : ℝ) : MeasurableSet (multiAnnulus N ε R) :=
  MeasurableSet.univ_pi (fun _ ↦ PolarAnnulus.measurableSet_annulus ε R)
theorem measurableSet_polarRectangle (N : ℕ) (ε R : ℝ) : MeasurableSet (polarRectangle N ε R) :=
  MeasurableSet.univ_pi (fun _ ↦ PolarAnnulus.measurableSet_rectangle ε R)

theorem integral_multiAnnulus_eq_polar {N : ℕ} (f : Space N → ℝ) (ε R : ℝ) (hε : 0 ≤ ε) :
    (∫ z in multiAnnulus N ε R, f z) = ∫ p in polarRectangle N ε R,
      (∏ i, (p i).1) * f (fun i ↦ Complex.polarCoord.symm (p i)) := by
  rw [← integral_indicator (measurableSet_multiAnnulus N ε R),
    ← Complex.integral_comp_pi_polarCoord_symm]
  have hind (p : Cart N) (hp : p ∈ univ.pi (fun _ ↦ Complex.polarCoord.target)) :
      (∏ i, (p i).1) • (multiAnnulus N ε R).indicator f (fun i ↦ Complex.polarCoord.symm (p i)) =
        (polarRectangle N ε R).indicator
          (fun q ↦ (∏ i, (q i).1) * f (fun i ↦ Complex.polarCoord.symm (q i))) p := by
    classical
    have hm : (fun i ↦ Complex.polarCoord.symm (p i)) ∈ multiAnnulus N ε R ↔ p ∈ polarRectangle N ε R := by
      constructor
      · intro hm i hi
        have hr := hm i hi
        change ε < ‖Complex.polarCoord.symm (p i)‖ ∧ ‖Complex.polarCoord.symm (p i)‖ < R at hr
        rw [Complex.norm_polarCoord_symm, abs_of_pos (hp i hi).1] at hr
        exact ⟨hr, (hp i hi).2⟩
      · intro hm i hi
        change ε < ‖Complex.polarCoord.symm (p i)‖ ∧ ‖Complex.polarCoord.symm (p i)‖ < R
        rw [Complex.norm_polarCoord_symm, abs_of_pos (hp i hi).1]
        exact (hm i hi).1
    by_cases h : (fun i ↦ Complex.polarCoord.symm (p i)) ∈ multiAnnulus N ε R
    · rw [indicator_of_mem h, indicator_of_mem (hm.mp h), smul_eq_mul]
    · rw [indicator_of_notMem h, indicator_of_notMem (mt hm.mpr h), smul_zero]
  calc
    _ = ∫ p in univ.pi (fun _ : Fin (N + 1) ↦ Complex.polarCoord.target),
        (polarRectangle N ε R).indicator
          (fun q ↦ (∏ i, (q i).1) * f (fun i ↦ Complex.polarCoord.symm (q i))) p :=
      setIntegral_congr_fun measurableSet_pi_polarCoord_target hind
    _ = _ := by
      rw [setIntegral_indicator (measurableSet_polarRectangle N ε R), inter_eq_right.mpr]
      intro p hp i hi
      exact PolarAnnulus.rectangle_subset_polarTarget hε (hp i hi)

theorem split_preimage_rectangle (N : ℕ) (ε R : ℝ) :
    splitMeas N ⁻¹' polarRectangle N ε R = finRectangle N ε R := by
  ext x
  constructor
  · intro hx j hj
    refine Fin.addCases (m := N + 1) (n := N + 1) (fun i ↦ ?_) (fun i ↦ ?_) j
    · simpa only [splitMeas_apply, split_apply, lower, upper, radiusIndex, angleIndex,
        Fin.addCases_left] using (hx i trivial).1
    · simpa only [splitMeas_apply, split_apply, lower, upper, radiusIndex, angleIndex,
        Fin.addCases_right] using (hx i trivial).2
  · intro hx i hi
    constructor
    · simpa only [splitMeas_apply, split_apply, lower_radius, upper_radius] using hx (radiusIndex i) trivial
    · simpa only [splitMeas_apply, split_apply, lower_angle, upper_angle] using hx (angleIndex i) trivial

theorem finRectangle_ae_eq_closed (N : ℕ) (ε R : ℝ) :
    finRectangle N ε R =ᵐ[volume] Icc (lower N ε) (upper N R) := by
  unfold finRectangle
  rw [volume_pi]
  exact Measure.univ_pi_Ioo_ae_eq_Icc

/-- Genuine simultaneous Pi polar change of variables, with the product radial Jacobian. -/
theorem integral_multiAnnulus_eq_box {N : ℕ} (f : Space N → ℝ) (ε R : ℝ)
    (hε : 0 ≤ ε) (hεR : ε < R) :
    (∫ z in multiAnnulus N ε R, f z) =
      ∫ x in BoxIntegral.Box.Icc (polarBox N ε R hεR),
        (∏ i, x (radiusIndex i)) * f (polar x) := by
  rw [integral_multiAnnulus_eq_polar f ε R hε]
  have h := (volume_preserving_split N).setIntegral_preimage_emb (splitMeas N).measurableEmbedding
    (fun p : Cart N ↦ (∏ i, (p i).1) * f (fun i ↦ Complex.polarCoord.symm (p i)))
    (polarRectangle N ε R)
  rw [split_preimage_rectangle N ε R] at h
  simp only [splitMeas_apply] at h
  simp_rw [← polar_eq_native] at h
  rw [← h, setIntegral_congr_set (finRectangle_ae_eq_closed N ε R)]
  rfl

def regularLocus (N : ℕ) : Set (Space N) := {z | ∀ i, z i ≠ 0}

theorem isOpen_regularLocus (N : ℕ) : IsOpen (regularLocus N) := by
  have heq : regularLocus N = ⋂ i : Fin (N + 1), {z : Space N | z i ≠ 0} := by
    ext z
    simp [regularLocus]
  rw [heq]
  exact isOpen_iInter_of_finite (fun i ↦ isOpen_ne_fun (continuous_apply i) continuous_const)

theorem polar_mem_regularLocus {N : ℕ} {x : Coord (Dim N)} (hx : ∀ i, 0 < x (radiusIndex i)) :
    polar x ∈ regularLocus N := by
  intro i
  exact PuncturedCoordinateStokes.polar_ne_zero (x := coordinatePair i x) (hx i)

def polarPullback {N : ℕ} (ω : CrossingForm N) : Form (Degree N) :=
  fun x ↦ (ω (polar x)).compContinuousLinearMap (fderiv ℝ polar x)

theorem polar_density {N : ℕ} (ω : CrossingForm N) (x : Coord (Dim N))
    (hω : DifferentiableAt ℝ ω (polar x)) :
    extDeriv (polarPullback ω) x (standardBasis (Dim N)) =
      (∏ i, x (radiusIndex i)) * density ω (polar x) := by
  unfold polarPullback
  rw [extDeriv_pullback hω (contDiff_polar N).contDiffAt (by simp), fderiv_polar,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  exact topForm_polar_frame (extDeriv ω (polar x)) x

theorem differentiableAt_polarPullback {N : ℕ} (ω : CrossingForm N) (x : Coord (Dim N))
    (hω : ContDiffAt ℝ 1 ω (polar x)) : DifferentiableAt ℝ (polarPullback ω) x := by
  apply DifferentiableAt.continuousAlternatingMapCompContinuousLinearMap
    ((hω.differentiableAt (by decide)).comp x (hasFDerivAt_polar x).differentiableAt)
  have hD : ContDiffAt ℝ 1 (fderiv ℝ (@polar N)) x :=
    (contDiff_polar N).contDiffAt.fderiv_right (by simp)
  exact hD.differentiableAt (by decide)

theorem continuousAt_density {N : ℕ} (ω : CrossingForm N) (z : Space N)
    (hω : ContDiffAt ℝ 1 ω z) : ContinuousAt (density ω) z :=
  (ContinuousAlternatingMap.apply ℝ _ ℝ (frame N)).continuous.continuousAt.comp
    ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ _ ℝ).continuous.continuousAt.comp
      (hω.continuousAt_fderiv (by decide)))

theorem regularity_on_polarBox {N : ℕ} (ω : CrossingForm N)
    (hω : ContDiffOn ℝ 1 ω (regularLocus N)) (ε R : ℝ) (hε : 0 < ε) (hεR : ε < R)
    (x : Coord (Dim N)) (hx : x ∈ BoxIntegral.Box.Icc (polarBox N ε R hεR)) :
    ContDiffAt ℝ 1 ω (polar x) := by
  apply hω.contDiffAt ((isOpen_regularLocus N).mem_nhds _)
  apply polar_mem_regularLocus
  intro i
  apply hε.trans_le
  simpa only [polarBox, lower_radius] using hx.1 (radiusIndex i)

/-- Genuine BoxStokes on the full simultaneous polar box. -/
theorem polar_box_stokes_all_faces {N : ℕ} (ω : CrossingForm N)
    (hω : ContDiffOn ℝ 1 ω (regularLocus N)) (ε R : ℝ) (hε : 0 < ε) (hεR : ε < R) :
    (∫ x in BoxIntegral.Box.Icc (polarBox N ε R hεR),
        (∏ i, x (radiusIndex i)) * density ω (polar x)) =
      ∑ j : Fin (Dim N), (-1 : ℝ) ^ j.val •
        ((∫ x in BoxIntegral.Box.Icc ((polarBox N ε R hεR).face j),
            facePullback (polarPullback ω) j ((polarBox N ε R hεR).upper j) x (standardBasis (Degree N))) -
          ∫ x in BoxIntegral.Box.Icc ((polarBox N ε R hεR).face j),
            facePullback (polarPullback ω) j ((polarBox N ε R hεR).lower j) x (standardBasis (Degree N))) := by
  let I := polarBox N ε R hεR
  have hc := regularity_on_polarBox ω hω ε R hε hεR
  have hd : EqOn (fun x ↦ extDeriv (polarPullback ω) x (standardBasis (Dim N)))
      (fun x ↦ (∏ i, x (radiusIndex i)) * density ω (polar x)) (BoxIntegral.Box.Icc I) :=
    fun x hx ↦ polar_density ω x ((hc x hx).differentiableAt (by decide))
  rw [← setIntegral_congr_fun I.isCompact_Icc.measurableSet hd]
  apply PuncturedProductStokes.integral_Icc_extDeriv_eq_faces_of_continuous
  · exact fun x hx ↦ differentiableAt_polarPullback ω x (hc x hx)
  · apply ContinuousOn.congr _ hd
    intro x hx
    have hp : Continuous (fun y : Coord (Dim N) ↦ ∏ i : Fin (N + 1), y (radiusIndex i)) := by fun_prop
    exact (hp.continuousAt.mul ((continuousAt_density ω (polar x) (hc x hx)).comp
      (contDiff_polar N).continuous.continuousAt)).continuousWithinAt

theorem faceEmbedding_other_eq {n : ℕ} (i j : Fin (n + 1)) (c c' : ℝ)
    (x : Coord n) (hji : j ≠ i) : faceEmbedding i c x j = faceEmbedding i c' x j := by
  induction j using i.succAboveCases with
  | x => exact False.elim (hji rfl)
  | p j => simp only [faceEmbedding, Fin.insertNth_apply_succAbove]

theorem circleParameter_angle_seam {N : ℕ} (i j : Fin (N + 1)) (x : Coord (Degree N)) :
    circleParameter (faceEmbedding (angleIndex i) Real.pi x (angleIndex j)) =
      circleParameter (faceEmbedding (angleIndex i) (-Real.pi) x (angleIndex j)) := by
  by_cases h : j = i
  · subst j
    simp only [faceEmbedding, Fin.insertNth_apply_same, PuncturedCoordinateStokes.circleParameter_seam]
  · rw [faceEmbedding_other_eq _ _ Real.pi (-Real.pi) x (by simpa using h)]

theorem angular_seams_equal {N : ℕ} (ω : CrossingForm N) (i : Fin (N + 1)) (x : Coord (Degree N)) :
    facePullback (polarPullback ω) (angleIndex i) Real.pi x (standardBasis (Degree N)) =
      facePullback (polarPullback ω) (angleIndex i) (-Real.pi) x (standardBasis (Degree N)) := by
  have hp : polar (faceEmbedding (angleIndex i) Real.pi x) =
      polar (faceEmbedding (angleIndex i) (-Real.pi) x) := by
    funext j
    simp only [polar_apply, LogCircle.shrinkingCircle, circleParameter_angle_seam]
    rw [faceEmbedding_other_eq _ _ Real.pi (-Real.pi) x (radiusIndex_ne_angleIndex j i)]
  have hD : polarDerivative (faceEmbedding (angleIndex i) Real.pi x) =
      polarDerivative (faceEmbedding (angleIndex i) (-Real.pi) x) := by
    ext v j
    simp only [polarDerivative_apply, hp, circleParameter_angle_seam]
  simp only [facePullback, polarPullback, fderiv_polar, fderiv_faceEmbedding, hp, hD]

def SupportBound {N : ℕ} (ω : CrossingForm N) (R : ℝ) : Prop :=
  ∀ z ∈ tsupport ω, ∀ i, ‖z i‖ < R

theorem exists_supportBound {N : ℕ} (ω : CrossingForm N) (hω : HasCompactSupport ω) :
    ∃ R : ℝ, 0 < R ∧ SupportBound ω R := by
  obtain ⟨R, hR, hb⟩ := hω.isCompact.isBounded.exists_pos_norm_lt
  exact ⟨R, hR, fun z hz i ↦ (norm_le_pi_norm z i).trans_lt (hb z hz)⟩

theorem outer_face_zero {N : ℕ} (ω : CrossingForm N) {R : ℝ} (hR : 0 ≤ R)
    (hbound : SupportBound ω R) (i : Fin (N + 1)) (x : Coord (Degree N)) :
    facePullback (polarPullback ω) (radiusIndex i) R x (standardBasis (Degree N)) = 0 := by
  have hz : ω (polar (faceEmbedding (radiusIndex i) R x)) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hn
    have h := hbound _ hn i
    simp only [polar_apply, LogCircle.norm_shrinkingCircle, faceEmbedding,
      Fin.insertNth_apply_same, abs_of_nonneg hR] at h
    exact lt_irrefl R h
  simp only [facePullback, polarPullback, hz]
  rfl

/-- The actual radial cylinder map; the other complex coordinates retain their polar parameters. -/
def cylinder {N : ℕ} (i : Fin (N + 1)) (r : ℝ) (x : Coord (Degree N)) : Space N :=
  polar (faceEmbedding (radiusIndex i) r x)

theorem hasFDerivAt_cylinder {N : ℕ} (i : Fin (N + 1)) (r : ℝ) (x : Coord (Degree N)) :
    HasFDerivAt (cylinder i r)
      ((polarDerivative (faceEmbedding (radiusIndex i) r x)).comp (faceTangent (radiusIndex i))) x :=
  (hasFDerivAt_polar _).comp x (hasFDerivAt_faceEmbedding (radiusIndex i) r x)

def cylinderDensity {N : ℕ} (ω : CrossingForm N) (i : Fin (N + 1)) (r : ℝ)
    (x : Coord (Degree N)) : ℝ :=
  (ω (cylinder i r x)).compContinuousLinearMap (fderiv ℝ (cylinder i r) x) (standardBasis (Degree N))

/-- Every other radial variable is cut at the same ε; no finite outer radius is part of this region. -/
def boundaryRegion {N : ℕ} (i : Fin (N + 1)) (ε : ℝ) : Set (Coord (Degree N)) :=
  {x | (∀ k, ε ≤ faceEmbedding (radiusIndex i) ε x (radiusIndex k)) ∧
    ∀ k, faceEmbedding (radiusIndex i) ε x (angleIndex k) ∈ Icc (-Real.pi) Real.pi}

def boundaryIntegral {N : ℕ} (ω : CrossingForm N) (i : Fin (N + 1)) (ε : ℝ) : ℝ :=
  ∫ x in boundaryRegion i ε, cylinderDensity ω i ε x

theorem measurableSet_boundaryRegion {N : ℕ} (i : Fin (N + 1)) (ε : ℝ) :
    MeasurableSet (boundaryRegion i ε) := by
  have hc : Continuous (faceEmbedding (radiusIndex i) ε) :=
    continuous_iff_continuousAt.mpr (fun x ↦ (hasFDerivAt_faceEmbedding (radiusIndex i) ε x).continuousAt)
  have hrad : MeasurableSet {x : Coord (Degree N) | ∀ k, ε ≤ faceEmbedding (radiusIndex i) ε x (radiusIndex k)} := by
    rw [show {x : Coord (Degree N) | ∀ k, ε ≤ faceEmbedding (radiusIndex i) ε x (radiusIndex k)} =
      ⋂ k, {x : Coord (Degree N) | ε ≤ faceEmbedding (radiusIndex i) ε x (radiusIndex k)} by ext x; simp]
    apply MeasurableSet.iInter
    intro k
    exact measurableSet_le measurable_const
      (((continuous_apply (radiusIndex k)).comp hc).measurable)
  have hang : MeasurableSet {x : Coord (Degree N) | ∀ k, faceEmbedding (radiusIndex i) ε x (angleIndex k) ∈ Icc (-Real.pi) Real.pi} := by
    rw [show {x : Coord (Degree N) | ∀ k, faceEmbedding (radiusIndex i) ε x (angleIndex k) ∈ Icc (-Real.pi) Real.pi} =
      ⋂ k, (fun x : Coord (Degree N) ↦ faceEmbedding (radiusIndex i) ε x (angleIndex k)) ⁻¹' Icc (-Real.pi) Real.pi by ext x; simp]
    apply MeasurableSet.iInter
    intro k
    exact measurableSet_Icc.preimage
      (((continuous_apply (angleIndex k)).comp hc).measurable)
  exact hrad.inter hang

theorem radial_face_density {N : ℕ} (ω : CrossingForm N) (i : Fin (N + 1))
    (r : ℝ) (x : Coord (Degree N)) :
    facePullback (polarPullback ω) (radiusIndex i) r x (standardBasis (Degree N)) =
      cylinderDensity ω i r x := by
  rw [cylinderDensity, (hasFDerivAt_cylinder i r x).fderiv]
  simp only [facePullback, polarPullback, fderiv_polar, fderiv_faceEmbedding,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, cylinder]
  rfl

theorem radial_face_subset_boundaryRegion {N : ℕ} (i : Fin (N + 1))
    (ε R : ℝ) (hεR : ε < R) :
    BoxIntegral.Box.Icc ((polarBox N ε R hεR).face (radiusIndex i)) ⊆ boundaryRegion i ε := by
  intro x hx
  have hm := (polarBox N ε R hεR).mapsTo_insertNth_face_Icc
    (i := radiusIndex i) (x := ε) (show ε ∈ Icc ((polarBox N ε R hεR).lower (radiusIndex i))
      ((polarBox N ε R hεR).upper (radiusIndex i)) by simpa [polarBox] using hεR.le) hx
  constructor
  · intro k
    simpa only [polarBox, lower_radius, faceEmbedding] using hm.1 (radiusIndex k)
  · intro k
    exact ⟨by simpa only [polarBox, lower_angle, faceEmbedding] using hm.1 (angleIndex k),
      by simpa only [polarBox, upper_angle, faceEmbedding] using hm.2 (angleIndex k)⟩

theorem cylinderDensity_zero_outside_box {N : ℕ} (ω : CrossingForm N) {R : ℝ}
    (hbound : SupportBound ω R) (i : Fin (N + 1)) (ε : ℝ) (hεR : ε < R)
    (x : Coord (Degree N)) (hx : x ∈ boundaryRegion i ε)
    (hn : x ∉ BoxIntegral.Box.Icc ((polarBox N ε R hεR).face (radiusIndex i))) :
    cylinderDensity ω i ε x = 0 := by
  by_contra hz
  have hω : ω (cylinder i ε x) ≠ 0 := by
    intro hw
    apply hz
    simp only [cylinderDensity, hw]
    rfl
  have hb (k : Fin (N + 1)) : |faceEmbedding (radiusIndex i) ε x (radiusIndex k)| < R := by
    have h := hbound _ (subset_tsupport ω hω) k
    simpa only [cylinder, polar_apply, LogCircle.norm_shrinkingCircle] using h
  have hm : faceEmbedding (radiusIndex i) ε x ∈ BoxIntegral.Box.Icc (polarBox N ε R hεR) := by
    constructor
    · intro j
      refine Fin.addCases (m := N + 1) (n := N + 1) (fun k ↦ ?_) (fun k ↦ ?_) j
      · simpa only [polarBox, radiusIndex, lower, Fin.addCases_left] using hx.1 k
      · simpa only [polarBox, angleIndex, lower, Fin.addCases_right] using (hx.2 k).1
    · intro j
      refine Fin.addCases (m := N + 1) (n := N + 1) (fun k ↦ ?_) (fun k ↦ ?_) j
      · simpa only [polarBox, radiusIndex, upper, Fin.addCases_left] using (le_abs_self _).trans (hb k).le
      · simpa only [polarBox, angleIndex, upper, Fin.addCases_right] using (hx.2 k).2
  exact hn (Fin.insertNth_mem_Icc.mp hm).2

theorem boundaryIntegral_eq_radial_face {N : ℕ} (ω : CrossingForm N) {R : ℝ}
    (hbound : SupportBound ω R) (i : Fin (N + 1)) (ε : ℝ) (hεR : ε < R) :
    boundaryIntegral ω i ε =
      ∫ x in BoxIntegral.Box.Icc ((polarBox N ε R hεR).face (radiusIndex i)),
        facePullback (polarPullback ω) (radiusIndex i) ε x (standardBasis (Degree N)) := by
  simp_rw [radial_face_density]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_boundaryRegion i ε)
    (radial_face_subset_boundaryRegion i ε R hεR)
  rintro x ⟨hx, hn⟩
  exact cylinderDensity_zero_outside_box ω hbound i ε hεR x hx hn

/-- The finite sum of inner radial faces is the entire boundary after actual seam
and support cancellation. Each lower radial face has sign -(-1)^i. -/
theorem polar_box_stokes {N : ℕ} (ω : CrossingForm N)
    (hω : ContDiffOn ℝ 1 ω (regularLocus N)) {R : ℝ} (hbound : SupportBound ω R)
    (ε : ℝ) (hε : 0 < ε) (hεR : ε < R) :
    (∫ x in BoxIntegral.Box.Icc (polarBox N ε R hεR),
      (∏ i, x (radiusIndex i)) * density ω (polar x)) =
      ∑ i : Fin (N + 1), -((-1 : ℝ) ^ i.val) • boundaryIntegral ω i ε := by
  rw [polar_box_stokes_all_faces ω hω ε R hε hεR]
  let I := polarBox N ε R hεR
  let F : Fin (Dim N) → ℝ → ℝ := fun j r ↦ ∫ x in BoxIntegral.Box.Icc (I.face j),
    facePullback (polarPullback ω) j r x (standardBasis (Degree N))
  change (∑ j : Fin (Dim N), (-1 : ℝ) ^ j.val • (F j (I.upper j) - F j (I.lower j))) = _
  have hsplit := Fin.sum_univ_add (a := N + 1) (b := N + 1)
    (fun j : Fin (Dim N) ↦ (-1 : ℝ) ^ j.val • (F j (I.upper j) - F j (I.lower j)))
  refine hsplit.trans ?_
  have hs (i : Fin (N + 1)) : F (angleIndex i) Real.pi = F (angleIndex i) (-Real.pi) := by
    apply setIntegral_congr_fun (I.face (angleIndex i)).isCompact_Icc.measurableSet
    exact fun x _ ↦ angular_seams_equal ω i x
  have ho (i : Fin (N + 1)) : F (radiusIndex i) R = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    exact fun x _ ↦ outer_face_zero ω (hε.trans hεR).le hbound i x
  have hsum : (∑ i : Fin (N + 1), (-1 : ℝ) ^ (angleIndex i).val •
      (F (angleIndex i) (I.upper (angleIndex i)) - F (angleIndex i) (I.lower (angleIndex i)))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    change (-1 : ℝ) ^ (angleIndex i).val • (F (angleIndex i) (upper N R (angleIndex i)) - F (angleIndex i) (lower N ε (angleIndex i))) = 0
    rw [upper_angle, lower_angle, hs i, sub_self, smul_zero]
  change (∑ i : Fin (N + 1), (-1 : ℝ) ^ (radiusIndex i).val •
      (F (radiusIndex i) (I.upper (radiusIndex i)) - F (radiusIndex i) (I.lower (radiusIndex i)))) +
    (∑ i : Fin (N + 1), (-1 : ℝ) ^ (angleIndex i).val •
      (F (angleIndex i) (I.upper (angleIndex i)) - F (angleIndex i) (I.lower (angleIndex i)))) = _
  rw [hsum, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  change (-1 : ℝ) ^ i.val • (F (radiusIndex i) (upper N R (radiusIndex i)) - F (radiusIndex i) (lower N ε (radiusIndex i))) = _
  have hb : F (radiusIndex i) ε = boundaryIntegral ω i ε :=
    (boundaryIntegral_eq_radial_face ω hbound i ε hεR).symm
  rw [upper_radius, lower_radius, ho i, zero_sub, hb, smul_neg, neg_smul]

/-- Stokes on the actual complex polyannulus, including simultaneous inner cutoffs. -/
theorem multiAnnulus_stokes {N : ℕ} (ω : CrossingForm N)
    (hω : ContDiffOn ℝ 1 ω (regularLocus N)) {R : ℝ} (hbound : SupportBound ω R)
    (ε : ℝ) (hε : 0 < ε) (hεR : ε < R) :
    (∫ z in multiAnnulus N ε R, density ω z) =
      ∑ i : Fin (N + 1), -((-1 : ℝ) ^ i.val) • boundaryIntegral ω i ε := by
  rw [integral_multiAnnulus_eq_box (density ω) ε R hε.le hεR]
  exact polar_box_stokes ω hω hbound ε hε hεR

def innerRegion (N : ℕ) (ε : ℝ) : Set (Space N) := {z | ∀ i, ε < ‖z i‖}
def innerCutoff {N : ℕ} (ε : ℝ) (f : Space N → ℝ) : Space N → ℝ := (innerRegion N ε).indicator f

theorem measurableSet_innerRegion (N : ℕ) (ε : ℝ) : MeasurableSet (innerRegion N ε) := by
  rw [show innerRegion N ε = ⋂ i : Fin (N + 1), {z : Space N | ε < ‖z i‖} by ext z; simp [innerRegion]]
  exact MeasurableSet.iInter (fun i ↦ measurableSet_lt measurable_const (measurable_pi_apply i).norm)

theorem ae_mem_regularLocus (N : ℕ) : ∀ᵐ z : Space N, z ∈ regularLocus N := by
  change ∀ᵐ z : Space N, ∀ i, z i ≠ 0
  rw [volume_pi, Filter.eventually_all]
  exact fun i ↦ Measure.ae_eval_ne (fun _ : Fin (N + 1) ↦ (volume : Measure ℂ)) i 0

theorem tendsto_innerCutoff_value {N : ℕ} (f : Space N → ℝ) (z : Space N)
    (hz : z ∈ regularLocus N) :
    Tendsto (fun ε : ℝ ↦ innerCutoff ε f z) (𝓝[>] 0) (𝓝 (f z)) := by
  have he : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ i, ε < ‖z i‖ := by
    apply Filter.eventually_all.mpr
    intro i
    exact (show ∀ᶠ ε : ℝ in 𝓝 0, ε < ‖z i‖ from
      Iio_mem_nhds (norm_pos_iff.mpr (hz i))).filter_mono nhdsWithin_le_nhds
  apply tendsto_const_nhds.congr'
  filter_upwards [he] with ε hε
  exact (indicator_of_mem (show z ∈ innerRegion N ε from hε) f).symm

/-- Actual simultaneous-cutoff L¹ convergence on the whole complex coordinate space. -/
theorem tendsto_innerCutoff_L1 {N : ℕ} (f : Space N → ℝ) (hf : Integrable f) :
    Tendsto (fun ε : ℝ ↦ ∫ z : Space N, ‖innerCutoff ε f z - f z‖) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝[>] (0 : ℝ)) (μ := (volume : Measure (Space N)))
    (F := fun ε z ↦ ‖innerCutoff ε f z - f z‖) (f := fun _ ↦ (0 : ℝ)) (fun z ↦ 2 * ‖f z‖)
    (Filter.Eventually.of_forall (fun ε ↦
      ((hf.aestronglyMeasurable.indicator (measurableSet_innerRegion N ε)).sub hf.aestronglyMeasurable).norm))
    (Filter.Eventually.of_forall (fun ε ↦ Filter.Eventually.of_forall (fun z ↦ ?_)))
    (hf.norm.const_mul 2) ?_
  · simpa only [integral_zero] using h
  · rw [Real.norm_of_nonneg (norm_nonneg _)]
    calc
      ‖innerCutoff ε f z - f z‖ ≤ ‖innerCutoff ε f z‖ + ‖f z‖ := norm_sub_le _ _
      _ ≤ ‖f z‖ + ‖f z‖ := add_le_add
        (norm_indicator_le_norm_self (s := innerRegion N ε) (f := f) (a := z)) le_rfl
      _ = 2 * ‖f z‖ := (two_mul _).symm
  · filter_upwards [ae_mem_regularLocus N] with z hz
    have hh := ((tendsto_innerCutoff_value f z hz).sub (tendsto_const_nhds (x := f z))).norm
    simpa only [sub_self, norm_zero] using hh

theorem tendsto_integral_innerCutoff {N : ℕ} (f : Space N → ℝ) (hf : Integrable f) :
    Tendsto (fun ε : ℝ ↦ ∫ z : Space N, innerCutoff ε f z) (𝓝[>] 0) (𝓝 (∫ z, f z)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun z ↦ ‖f z‖)
  · exact Filter.Eventually.of_forall (fun ε ↦ hf.aestronglyMeasurable.indicator (measurableSet_innerRegion N ε))
  · exact Filter.Eventually.of_forall (fun ε ↦ Filter.Eventually.of_forall
      (fun z ↦ norm_indicator_le_norm_self (f := f) (a := z)))
  · exact hf.norm
  · filter_upwards [ae_mem_regularLocus N] with z hz
    exact tendsto_innerCutoff_value f z hz

theorem integral_innerCutoff_density_eq_multiAnnulus {N : ℕ} (ω : CrossingForm N)
    {R : ℝ} (hbound : SupportBound ω R) (ε : ℝ) :
    (∫ z : Space N, innerCutoff ε (density ω) z) =
      ∫ z in multiAnnulus N ε R, density ω z := by
  rw [innerCutoff, integral_indicator (measurableSet_innerRegion N ε)]
  apply CompactSupportBoxes.setIntegral_eq_of_support_inter_subset _ _ _ (measurableSet_innerRegion N ε)
  · intro z hz i
    exact (hz i trivial).1
  · rintro z ⟨hz, hε⟩ i hi
    have hs := CompactSupportBoxes.support_extDeriv_apply_subset ω (frame N) hz
    exact ⟨hε i, hbound z hs i⟩

/-- Actual normal-crossing Stokes: every singular divisor remains removed until
the simultaneous L¹ limit; the only boundary hypotheses are genuine flux limits. -/
theorem integral_extDeriv_eq_zero {N : ℕ} (ω : CrossingForm N)
    (hω : ContDiffOn ℝ 1 ω (regularLocus N)) (hcompact : HasCompactSupport ω)
    (hL1 : Integrable (density ω))
    (hboundary : ∀ i : Fin (N + 1), Tendsto (boundaryIntegral ω i) (𝓝[>] 0) (𝓝 0)) :
    (∫ z : Space N, density ω z) = 0 := by
  obtain ⟨R, hR, hbound⟩ := exists_supportBound ω hcompact
  have hlim := tendsto_integral_innerCutoff (density ω) hL1
  have heq : (fun ε : ℝ ↦ ∫ z : Space N, innerCutoff ε (density ω) z) =ᶠ[𝓝[>] 0]
      (fun ε ↦ ∑ i : Fin (N + 1), -((-1 : ℝ) ^ i.val) • boundaryIntegral ω i ε) := by
    filter_upwards [Ioo_mem_nhdsGT hR] with ε hε
    rw [integral_innerCutoff_density_eq_multiAnnulus ω hbound ε,
      multiAnnulus_stokes ω hω hbound ε hε.1 hε.2]
  have hz : Tendsto (fun ε ↦ ∑ i : Fin (N + 1), -((-1 : ℝ) ^ i.val) • boundaryIntegral ω i ε)
      (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_finsetSum Finset.univ (fun i hi ↦ (hboundary i).const_smul (-((-1 : ℝ) ^ i.val)))
    simpa only [smul_zero, Finset.sum_const_zero] using h
  exact tendsto_nhds_unique hlim (hz.congr' heq.symm)

theorem integral_extDeriv_frame_eq_zero {N : ℕ} (ω : CrossingForm N)
    (hω : ContDiffOn ℝ 1 ω (regularLocus N)) (hcompact : HasCompactSupport ω)
    (hL1 : Integrable (fun z ↦ extDeriv ω z (frame N)))
    (hboundary : ∀ i : Fin (N + 1), Tendsto (boundaryIntegral ω i) (𝓝[>] 0) (𝓝 0)) :
    (∫ z : Space N, extDeriv ω z (frame N)) = 0 :=
  integral_extDeriv_eq_zero ω hω hcompact hL1 hboundary

/-- Every positive simultaneous cutoff gives a genuine finite boundary integral. -/
theorem integrableOn_cylinderDensity {N : ℕ} (ω : CrossingForm N)
    (hω : ContDiffOn ℝ 1 ω (regularLocus N)) (hcompact : HasCompactSupport ω)
    (i : Fin (N + 1)) (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (cylinderDensity ω i ε) (boundaryRegion i ε) := by
  obtain ⟨R₀, hR₀, hb⟩ := exists_supportBound ω hcompact
  let R := R₀ + ε
  have hεR : ε < R := by dsimp [R]; linarith
  have hbound : SupportBound ω R := fun z hz j ↦
    (hb z hz j).trans (lt_add_of_pos_right R₀ hε)
  let I := polarBox N ε R hεR
  have hc : ContinuousOn (polarPullback ω) (BoxIntegral.Box.Icc I) := fun x hx ↦
    (differentiableAt_polarPullback ω x (regularity_on_polarBox ω hω ε R hε hεR x hx)).continuousAt.continuousWithinAt
  have hface := BoxStokes.integrableOn_face_density I (polarPullback ω) hc (radiusIndex i)
    (c := ε) (by simpa only [I, polarBox, lower_radius, upper_radius, mem_Icc, le_refl, true_and] using hεR.le)
  have hf : IntegrableOn (cylinderDensity ω i ε) (BoxIntegral.Box.Icc (I.face (radiusIndex i))) := by
    simpa only [radial_face_density] using hface
  apply hf.of_forall_sdiff_eq_zero (measurableSet_boundaryRegion i ε)
  rintro x ⟨hx, hn⟩
  exact cylinderDensity_zero_outside_box ω hbound i ε hεR x hx hn

/-- The one-complex-coordinate lift is the actual form pullback along evaluation at zero. -/
def liftOne (ω : PuncturedCoordinateStokes.OneForm) : CrossingForm 0 :=
  fun z ↦ (ω (z 0)).compContinuousLinearMap (ContinuousLinearMap.proj 0)

theorem density_liftOne (ω : PuncturedCoordinateStokes.OneForm) (z : Space 0)
    (hω : DifferentiableAt ℝ ω (z 0)) : density (liftOne ω) z = PuncturedCoordinateStokes.density ω (z 0) := by
  unfold density liftOne
  have h := extDeriv_pullback (r := ⊤)
    (f := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 ↦ ℂ) 0)) hω
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 ↦ ℂ) 0).contDiff.contDiffAt (by simp)
  simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.proj_apply] at h
  rw [h, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  change extDeriv ω (z 0) _ = extDeriv ω (z 0) ![1, Complex.I]
  congr 1
  funext i
  fin_cases i <;> simp [frame, complexConvert, split, standardBasis, radiusIndex, angleIndex, Complex.equivRealProdCLM_symm_apply]

theorem cylinderDensity_liftOne (ω : PuncturedCoordinateStokes.OneForm)
    (r : ℝ) (x : Coord 1) :
    cylinderDensity (liftOne ω) 0 r x = PuncturedCoordinateStokes.circleDensity ω r (x 0) := by
  rw [← radial_face_density, facePullback_standardBasis]
  unfold faceCoefficient polarPullback liftOne
  simp only [fderiv_polar, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  change ω (LogCircle.shrinkingCircle r (x 0)) _ = _
  congr 1
  funext i
  rw [Subsingleton.elim i 0]
  change polarDerivative (faceEmbedding (radiusIndex (0 : Fin 1)) r x) (standardBasis 2 1) 0 =
    LogCircle.shrinkingCircleTangent r (x 0) 1
  rw [polarDerivative_apply]
  simp [standardBasis, polar_apply, radiusIndex, angleIndex, faceEmbedding,
    Fin.insertNth_zero', LogCircle.shrinkingCircleTangent_apply]

theorem boundaryRegion_one (r : ℝ) :
    boundaryRegion (0 : Fin 1) r = Icc (fun _ : Fin 1 ↦ -Real.pi) (fun _ ↦ Real.pi) := by
  ext x
  simp [boundaryRegion, radiusIndex, angleIndex, faceEmbedding, Fin.insertNth_zero',
    Pi.le_def, Fin.forall_fin_one]

theorem boundaryIntegral_liftOne (ω : PuncturedCoordinateStokes.OneForm) (r : ℝ) :
    boundaryIntegral (liftOne ω) 0 r = PuncturedCoordinateStokes.circleIntegral ω r := by
  unfold boundaryIntegral
  simp_rw [cylinderDensity_liftOne]
  rw [boundaryRegion_one, PuncturedCoordinateStokes.integral_finOne_Icc,
    PuncturedCoordinateStokes.circleIntegral_eq_centered,
    intervalIntegral.integral_of_le (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos]),
    setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]

theorem integral_density_liftOne (ω : PuncturedCoordinateStokes.OneForm)
    (hω : ContDiffOn ℝ 1 ω ({0}ᶜ : Set ℂ)) :
    (∫ z : Space 0, density (liftOne ω) z) = ∫ z : ℂ, PuncturedCoordinateStokes.density ω z := by
  have heq : density (liftOne ω) =ᵐ[volume] (fun z : Space 0 ↦ PuncturedCoordinateStokes.density ω (z 0)) := by
    filter_upwards [ae_mem_regularLocus 0] with z hz
    exact density_liftOne ω z ((hω.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds (hz 0))).differentiableAt (by decide))
  rw [integral_congr_ae heq]
  exact (volume_preserving_funUnique (Fin 1) ℂ).integral_comp
    (MeasurableEquiv.funUnique (Fin 1) ℂ).measurableEmbedding _

theorem contDiffOn_liftOne (ω : PuncturedCoordinateStokes.OneForm)
    (hω : ContDiffOn ℝ 1 ω ({0}ᶜ : Set ℂ)) : ContDiffOn ℝ 1 (liftOne ω) (regularLocus 0) := by
  intro z hz
  have hc := hω.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds (hz 0))
  exact ((ContinuousAlternatingMap.compContinuousLinearMapCLM
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 ↦ ℂ) 0)).contDiff.contDiffAt.comp z
      (hc.comp z (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 ↦ ℂ) 0).contDiff.contDiffAt)).contDiffWithinAt

theorem hasCompactSupport_liftOne (ω : PuncturedCoordinateStokes.OneForm)
    (hω : HasCompactSupport ω) : HasCompactSupport (liftOne ω) := by
  have h := hω.comp_homeomorph (Homeomorph.funUnique (Fin 1) ℂ)
  exact h.comp_left (g := ContinuousAlternatingMap.compContinuousLinearMapCLM
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 ↦ ℂ) 0)) (map_zero _)

theorem integrable_density_liftOne (ω : PuncturedCoordinateStokes.OneForm)
    (hω : ContDiffOn ℝ 1 ω ({0}ᶜ : Set ℂ)) (hL1 : Integrable (PuncturedCoordinateStokes.density ω)) :
    Integrable (density (liftOne ω)) := by
  have h := ((volume_preserving_funUnique (Fin 1) ℂ).integrable_comp_emb
    (MeasurableEquiv.funUnique (Fin 1) ℂ).measurableEmbedding
    (g := PuncturedCoordinateStokes.density ω)).mpr hL1
  apply h.congr
  filter_upwards [ae_mem_regularLocus 0] with z hz
  exact (density_liftOne ω z ((hω.contDiffAt
    (isClosed_singleton.isOpen_compl.mem_nhds (hz 0))).differentiableAt (by decide))).symm

/-- One complex coordinate recovers the old theorem with precisely its old hypotheses,
now as a specialization of simultaneous normal-crossing Stokes. -/
theorem one_coordinate_recovers_stokes (ω : PuncturedCoordinateStokes.OneForm)
    (hω : ContDiffOn ℝ 1 ω ({0}ᶜ : Set ℂ)) (hcompact : HasCompactSupport ω)
    (hL1 : Integrable (PuncturedCoordinateStokes.density ω))
    (hcircle : Tendsto (PuncturedCoordinateStokes.circleIntegral ω) (𝓝[>] 0) (𝓝 0)) :
    (∫ z : ℂ, extDeriv ω z ![1, Complex.I]) = 0 := by
  have hb : ∀ i : Fin 1, Tendsto (boundaryIntegral (liftOne ω) i) (𝓝[>] 0) (𝓝 0) := by
    intro i
    rw [Subsingleton.elim i 0]
    have heq : boundaryIntegral (liftOne ω) 0 = PuncturedCoordinateStokes.circleIntegral ω :=
      funext (boundaryIntegral_liftOne ω)
    rwa [heq]
  have h := integral_extDeriv_eq_zero (liftOne ω) (contDiffOn_liftOne ω hω)
    (hasCompactSupport_liftOne ω hcompact) (integrable_density_liftOne ω hω hL1) hb
  rwa [integral_density_liftOne ω hω] at h

/-- The displayed top frame really is the ordinary real coordinate basis of ℂ^(N+1). -/
theorem frame_radius {N : ℕ} (i : Fin (N + 1)) : frame N (radiusIndex i) = Pi.single i 1 := by
  funext k
  simp [frame, complexConvert, split, standardBasis, Pi.single_apply,
    Complex.equivRealProdCLM_symm_apply]
  split_ifs <;> simp

theorem frame_angle {N : ℕ} (i : Fin (N + 1)) : frame N (angleIndex i) = Pi.single i Complex.I := by
  funext k
  simp [frame, complexConvert, split, standardBasis, Pi.single_apply,
    Complex.equivRealProdCLM_symm_apply]
  split_ifs <;> simp

end EnvelopingIsomorphism.Deformation.Kontsevich.NormalCrossingStokes
