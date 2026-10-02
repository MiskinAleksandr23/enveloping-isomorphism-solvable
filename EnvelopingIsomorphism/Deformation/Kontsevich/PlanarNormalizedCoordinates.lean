import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarClusterCompactification
import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFiberAngleSplit
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Complex

/-! Global circle/unit-shape coordinates on normalized planar configurations,
and genuine holomorphic changes of the chosen reference pair. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PlanarNormalizedCoordinates

open Set Topology InteriorFiberAngleSplit

abbrev Normalized (N : ℕ) := PlanarClusterCompactification.Normalized (0 : Point N) 1
abbrev Configuration (N : ℕ) := {η : Shape N // η ∈ shapeConfiguration N}

def phase {N : ℕ} (z : Normalized N) : Circle :=
  ⟨z.val 1, mem_sphere_zero_iff_norm.mpr z.property.2.2⟩

theorem reference_ne_zero {N : ℕ} (z : Normalized N) : z.val 1 ≠ 0 := (phase z).coe_ne_zero

def shape {N : ℕ} (z : Normalized N) : Shape N := fun j ↦ z.val j.succ.succ / z.val 1

theorem normalizedPoint_shape {N : ℕ} (z : Normalized N) (j : Point N) :
    normalizedPoint (shape z) j = z.val j / z.val 1 := by
  refine Fin.cases ?_ (fun k ↦ Fin.cases ?_ (fun l ↦ ?_) k) j
  · rw [normalizedPoint_anchor, z.property.2.1, zero_div]
  · rw [show (Fin.succ (0 : Fin (N + 1)) : Point N) = 1 from rfl,
      normalizedPoint_reference, div_self (reference_ne_zero z)]
  · rfl

theorem shape_mem_configuration {N : ℕ} (z : Normalized N) : shape z ∈ shapeConfiguration N := by
  intro s t h
  apply z.property.1
  rw [normalizedPoint_shape, normalizedPoint_shape] at h
  have hh := congrArg (fun w : ℂ ↦ w * z.val 1) h
  simpa only [div_mul_cancel₀ _ (reference_ne_zero z)] using hh

def toCoordinates {N : ℕ} (z : Normalized N) : Circle × Configuration N :=
  (phase z, ⟨shape z, shape_mem_configuration z⟩)

def restore {N : ℕ} (p : Circle × Configuration N) (j : Point N) : ℂ :=
  (p.1 : ℂ) * normalizedPoint p.2.val j

def ofCoordinates {N : ℕ} (p : Circle × Configuration N) : Normalized N := by
  refine ⟨restore p, ?_, ?_, ?_⟩
  · intro s t h
    apply p.2.property
    exact mul_left_cancel₀ p.1.coe_ne_zero h
  · simp [restore]
  · simp [restore]

theorem ofCoordinates_toCoordinates {N : ℕ} (z : Normalized N) : ofCoordinates (toCoordinates z) = z := by
  apply Subtype.ext
  funext j
  change z.val 1 * normalizedPoint (shape z) j = z.val j
  rw [normalizedPoint_shape]
  field_simp [reference_ne_zero z]

theorem toCoordinates_ofCoordinates {N : ℕ} (p : Circle × Configuration N) : toCoordinates (ofCoordinates p) = p := by
  apply Prod.ext
  · apply Circle.ext
    change restore p 1 = (p.1 : ℂ)
    simp [restore]
  · apply Subtype.ext
    funext j
    change restore p j.succ.succ / restore p 1 = p.2.val j
    simp [restore, p.1.coe_ne_zero]

theorem continuous_toCoordinates (N : ℕ) : Continuous (@toCoordinates N) := by
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    exact (continuous_apply 1).comp continuous_subtype_val
  · apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    exact ((continuous_apply j.succ.succ).comp continuous_subtype_val).div
      ((continuous_apply 1).comp continuous_subtype_val) (fun z ↦ reference_ne_zero z)

theorem continuous_ofCoordinates (N : ℕ) : Continuous (@ofCoordinates N) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  have hphase : Continuous (fun p : Circle × Configuration N ↦ (p.1 : ℂ)) :=
    continuous_subtype_val.comp continuous_fst
  have hshape : Continuous (fun p : Circle × Configuration N ↦ p.2.val) :=
    continuous_subtype_val.comp continuous_snd
  exact hphase.mul ((contDiff_normalizedPoint j).continuous.comp hshape)

/-- Actual global coordinates on the whole original normalized planar fiber. -/
def homeomorph (N : ℕ) : Normalized N ≃ₜ Circle × Configuration N where
  toFun := toCoordinates
  invFun := ofCoordinates
  left_inv := ofCoordinates_toCoordinates
  right_inv := toCoordinates_ofCoordinates
  continuous_toFun := continuous_toCoordinates N
  continuous_invFun := continuous_ofCoordinates N

theorem ofCoordinates_circleExp {N : ℕ} (θ : ℝ) (η : Configuration N) :
    (ofCoordinates (Circle.exp θ, η)).val = rotatedPoint (θ, η.val) := by
  funext j
  change (Circle.exp θ : ℂ) * normalizedPoint η.val j = circleParameter θ * normalizedPoint η.val j
  rw [circleParameter_eq]

theorem coordinates_rotatedPoint {N : ℕ} (θ : ℝ) (η : Shape N) (hη : η ∈ shapeConfiguration N) :
    toCoordinates ⟨rotatedPoint (θ, η), rotatedPoint_normalization (θ, η) hη⟩ = (Circle.exp θ, ⟨η, hη⟩) := by
  have heq : (⟨rotatedPoint (θ, η), rotatedPoint_normalization (θ, η) hη⟩ : Normalized N) =
      ofCoordinates (Circle.exp θ, ⟨η, hη⟩) := by
    apply Subtype.ext
    exact (ofCoordinates_circleExp θ ⟨η, hη⟩).symm
  rw [heq, toCoordinates_ofCoordinates]

/-- New canonical labels are sent to old labels; σ(0),σ(1) are the chosen reference pair. -/
def referenceChange {N : ℕ} (σ : Equiv.Perm (Point N)) (η : Shape N) : Shape N := fun j ↦
  (normalizedPoint η (σ j.succ.succ) - normalizedPoint η (σ 0)) /
    (normalizedPoint η (σ 1) - normalizedPoint η (σ 0))

theorem reference_denominator_ne_zero {N : ℕ} (σ : Equiv.Perm (Point N))
    {η : Shape N} (hη : η ∈ shapeConfiguration N) :
    normalizedPoint η (σ 1) - normalizedPoint η (σ 0) ≠ 0 :=
  shapeDifference_ne_zero hη (σ.injective.ne Fin.zero_ne_one)

/-- The affine reference-pair quotient describes every new point, including the marks. -/
theorem normalizedPoint_referenceChange {N : ℕ} (σ : Equiv.Perm (Point N))
    {η : Shape N} (hη : η ∈ shapeConfiguration N) (j : Point N) :
    normalizedPoint (referenceChange σ η) j =
      (normalizedPoint η (σ j) - normalizedPoint η (σ 0)) /
        (normalizedPoint η (σ 1) - normalizedPoint η (σ 0)) := by
  refine Fin.cases ?_ (fun k ↦ Fin.cases ?_ (fun l ↦ ?_) k) j
  · simp
  · simpa using (div_self (reference_denominator_ne_zero σ hη)).symm
  · rfl

theorem referenceChange_mem_configuration {N : ℕ} (σ : Equiv.Perm (Point N))
    {η : Shape N} (hη : η ∈ shapeConfiguration N) : referenceChange σ η ∈ shapeConfiguration N := by
  intro s t h
  rw [normalizedPoint_referenceChange σ hη, normalizedPoint_referenceChange σ hη] at h
  have hh := congrArg (fun z : ℂ ↦ z * (normalizedPoint η (σ 1) - normalizedPoint η (σ 0))) h
  simp only [div_mul_cancel₀ _ (reference_denominator_ne_zero σ hη)] at hh
  exact σ.injective (hη (sub_left_inj.mp hh))

@[simp] theorem referenceChange_refl {N : ℕ} (η : Shape N) : referenceChange (Equiv.refl (Point N)) η = η := by
  funext j
  simp [referenceChange]

theorem quotient_difference_cancel (z w a b d : ℂ) (hd : d ≠ 0) :
    ((z - a) / d - (w - a) / d) / ((b - a) / d - (w - a) / d) = (z - w) / (b - w) := by
  rw [← sub_div, ← sub_div]
  have hn : (z - a) - (w - a) = z - w := by abel
  have hb : (b - a) - (w - a) = b - w := by abel
  rw [hn, hb, div_div_div_cancel_right₀ hd]

/-- Actual reference changes compose by the actual label permutations. -/
theorem referenceChange_comp {N : ℕ} (σ τ : Equiv.Perm (Point N))
    {η : Shape N} (hη : η ∈ shapeConfiguration N) :
    referenceChange τ (referenceChange σ η) = referenceChange (τ.trans σ) η := by
  funext j
  simp only [referenceChange, normalizedPoint_referenceChange σ hη, Equiv.trans_apply]
  exact quotient_difference_cancel _ _ _ _ _ (reference_denominator_ne_zero σ hη)

theorem referenceChange_symm_apply {N : ℕ} (σ : Equiv.Perm (Point N))
    {η : Shape N} (hη : η ∈ shapeConfiguration N) : referenceChange σ.symm (referenceChange σ η) = η := by
  simpa only [Equiv.symm_trans_self, referenceChange_refl] using referenceChange_comp σ σ.symm hη

theorem referenceChange_apply_symm {N : ℕ} (σ : Equiv.Perm (Point N))
    {η : Shape N} (hη : η ∈ shapeConfiguration N) : referenceChange σ (referenceChange σ.symm η) = η := by
  simpa only [Equiv.self_trans_symm, referenceChange_refl] using referenceChange_comp σ.symm σ hη

theorem analyticAt_normalizedPoint {N : ℕ} (j : Point N) (η : Shape N) :
    AnalyticAt ℂ (fun ζ : Shape N ↦ normalizedPoint ζ j) η := by
  refine Fin.cases ?_ (fun k ↦ Fin.cases ?_ (fun l ↦ ?_) k) j
  · exact analyticAt_const
  · exact analyticAt_const
  · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N ↦ ℂ) l).analyticAt η

/-- The true rational reference change is complex analytic on the collision complement. -/
theorem analyticOnNhd_referenceChange {N : ℕ} (σ : Equiv.Perm (Point N)) :
    AnalyticOnNhd ℂ (referenceChange σ) (shapeConfiguration N) := by
  intro η hη
  apply AnalyticAt.pi
  intro j
  exact ((analyticAt_normalizedPoint (σ j.succ.succ) η).sub (analyticAt_normalizedPoint (σ 0) η)).div
    ((analyticAt_normalizedPoint (σ 1) η).sub (analyticAt_normalizedPoint (σ 0) η))
    (reference_denominator_ne_zero σ hη)

def referenceCoordinates {N : ℕ} (σ : Equiv.Perm (Point N)) (η : Configuration N) : Configuration N :=
  ⟨referenceChange σ η.val, referenceChange_mem_configuration σ η.property⟩

theorem continuous_referenceCoordinates {N : ℕ} (σ : Equiv.Perm (Point N)) : Continuous (referenceCoordinates σ) := by
  apply Continuous.subtype_mk
  apply continuous_iff_continuousAt.mpr
  intro η
  exact ((analyticOnNhd_referenceChange σ) η.val η.property).continuousAt.comp continuous_subtype_val.continuousAt

/-- The actual reference-pair changes are global biholomorphic maps of unit shapes. -/
def referenceHomeomorph {N : ℕ} (σ : Equiv.Perm (Point N)) : Configuration N ≃ₜ Configuration N where
  toFun := referenceCoordinates σ
  invFun := referenceCoordinates σ.symm
  left_inv η := Subtype.ext (referenceChange_symm_apply σ η.property)
  right_inv η := Subtype.ext (referenceChange_apply_symm σ η.property)
  continuous_toFun := continuous_referenceCoordinates σ
  continuous_invFun := continuous_referenceCoordinates σ.symm

/-- Differentiating the actual inverse identity gives the actual inverse complex differential. -/
theorem fderiv_inverse_comp {N : ℕ} (σ : Equiv.Perm (Point N))
    {η : Shape N} (hη : η ∈ shapeConfiguration N) :
    (fderiv ℂ (referenceChange σ.symm) (referenceChange σ η)).comp
      (fderiv ℂ (referenceChange σ) η) = ContinuousLinearMap.id ℂ (Shape N) := by
  have hnew := referenceChange_mem_configuration σ hη
  have h := (((analyticOnNhd_referenceChange σ.symm) _ hnew).differentiableAt.hasFDerivAt).comp η
    (((analyticOnNhd_referenceChange σ) _ hη).differentiableAt.hasFDerivAt)
  have heq : (referenceChange σ.symm ∘ referenceChange σ) =ᶠ[nhds η] id := by
    filter_upwards [(isOpen_shapeConfiguration N).mem_nhds hη] with ζ hζ
    exact referenceChange_symm_apply σ hζ
  have hD := h.fderiv
  rw [heq.fderiv_eq, fderiv_id] at hD
  exact hD.symm

theorem fderiv_comp_inverse {N : ℕ} (σ : Equiv.Perm (Point N))
    {η : Shape N} (hη : η ∈ shapeConfiguration N) :
    (fderiv ℂ (referenceChange σ) η).comp
      (fderiv ℂ (referenceChange σ.symm) (referenceChange σ η)) = ContinuousLinearMap.id ℂ (Shape N) := by
  have h := fderiv_inverse_comp σ.symm (referenceChange_mem_configuration σ hη)
  simpa only [Equiv.symm_symm, referenceChange_symm_apply σ hη] using h

theorem fderiv_referenceChange_bijective {N : ℕ} (σ : Equiv.Perm (Point N))
    {η : Shape N} (hη : η ∈ shapeConfiguration N) :
    Function.Bijective (fderiv ℂ (referenceChange σ) η) := by
  have hl : Function.LeftInverse (fderiv ℂ (referenceChange σ.symm) (referenceChange σ η))
      (fderiv ℂ (referenceChange σ) η) := fun v ↦
    congrArg (fun L : Shape N →L[ℂ] Shape N ↦ L v) (fderiv_inverse_comp σ hη)
  have hr : Function.RightInverse (fderiv ℂ (referenceChange σ.symm) (referenceChange σ η))
      (fderiv ℂ (referenceChange σ) η) := fun v ↦
    congrArg (fun L : Shape N →L[ℂ] Shape N ↦ L v) (fderiv_comp_inverse σ hη)
  exact ⟨hl.injective, hr.surjective⟩

theorem complexJacobian_ne_zero {N : ℕ} (σ : Equiv.Perm (Point N))
    {η : Shape N} (hη : η ∈ shapeConfiguration N) : (fderiv ℂ (referenceChange σ) η).det ≠ 0 := by
  change LinearMap.det (fderiv ℂ (referenceChange σ) η).toLinearMap ≠ 0
  intro hz
  have h := congrArg (fun L : Shape N →L[ℂ] Shape N ↦ LinearMap.det L.toLinearMap)
    (fderiv_inverse_comp σ hη)
  change LinearMap.det ((fderiv ℂ (referenceChange σ.symm) (referenceChange σ η)).toLinearMap.comp
    (fderiv ℂ (referenceChange σ) η).toLinearMap) = LinearMap.det (LinearMap.id : Shape N →ₗ[ℂ] Shape N) at h
  rw [LinearMap.det_comp, LinearMap.det_id, hz, mul_zero] at h
  exact zero_ne_one h

/-- The actual real Jacobian is the squared norm of the actual complex determinant. -/
theorem realJacobian_eq_norm_sq {N : ℕ} (σ : Equiv.Perm (Point N))
    {η : Shape N} (hη : η ∈ shapeConfiguration N) :
    (fderiv ℝ (referenceChange σ) η).det = ‖(fderiv ℂ (referenceChange σ) η).det‖ ^ 2 := by
  rw [((analyticOnNhd_referenceChange σ) η hη).differentiableAt.fderiv_restrictScalars (𝕜 := ℝ)]
  change LinearMap.det ((fderiv ℂ (referenceChange σ) η).toLinearMap.restrictScalars ℝ) = _
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]

/-- Every genuine holomorphic reference transition preserves the real orientation. -/
theorem realJacobian_pos {N : ℕ} (σ : Equiv.Perm (Point N))
    {η : Shape N} (hη : η ∈ shapeConfiguration N) : 0 < (fderiv ℝ (referenceChange σ) η).det := by
  rw [realJacobian_eq_norm_sq σ hη]
  exact pow_pos (norm_pos_iff.mpr (complexJacobian_ne_zero σ hη)) 2

/-- A literal permutation choosing any distinct old labels as the new marks. -/
def referencePermutation {N : ℕ} (a b : Point N) : Equiv.Perm (Point N) :=
  (Equiv.swap 1 ((Equiv.swap 0 a).symm b)).trans (Equiv.swap 0 a)

theorem referencePermutation_reference {N : ℕ} (a b : Point N) : referencePermutation a b 1 = b := by
  simp [referencePermutation]

theorem referencePermutation_anchor {N : ℕ} (a b : Point N) (hab : a ≠ b) : referencePermutation a b 0 = a := by
  let τ := Equiv.swap (0 : Point N) a
  have ha : τ 0 = a := Equiv.swap_apply_left _ _
  have hk : (0 : Point N) ≠ τ.symm b := by
    intro h
    have hh := congrArg τ h
    rw [τ.apply_symm_apply] at hh
    exact hab (ha.symm.trans hh)
  change τ (Equiv.swap 1 (τ.symm b) 0) = a
  rw [Equiv.swap_apply_of_ne_of_ne Fin.zero_ne_one hk, ha]

theorem referenceChange_marked_formula {N : ℕ} (a b : Point N) (hab : a ≠ b)
    {η : Shape N} (hη : η ∈ shapeConfiguration N) (j : Point N) :
    normalizedPoint (referenceChange (referencePermutation a b) η) j =
      (normalizedPoint η (referencePermutation a b j) - normalizedPoint η a) /
        (normalizedPoint η b - normalizedPoint η a) := by
  rw [normalizedPoint_referenceChange _ hη, referencePermutation_anchor a b hab,
    referencePermutation_reference]

def renormalizedPositions {N : ℕ} (σ : Equiv.Perm (Point N)) (z : Normalized N) (j : Point N) : ℂ :=
  (z.val (σ j) - z.val (σ 0)) / (‖z.val (σ 1) - z.val (σ 0)‖ : ℂ)

theorem renormalization_scale_ne_zero {N : ℕ} (σ : Equiv.Perm (Point N)) (z : Normalized N) :
    (‖z.val (σ 1) - z.val (σ 0)‖ : ℂ) ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (z.property.1.ne (σ.injective.ne Fin.zero_ne_one.symm)))

/-- Actual translation, positive-scale normalization, and label change of the original fiber. -/
def renormalize {N : ℕ} (σ : Equiv.Perm (Point N)) (z : Normalized N) : Normalized N := by
  refine ⟨renormalizedPositions σ z, ?_, ?_, ?_⟩
  · intro j k h
    have hh := congrArg (fun v : ℂ ↦ v * (‖z.val (σ 1) - z.val (σ 0)‖ : ℂ)) h
    simp only [renormalizedPositions, div_mul_cancel₀ _ (renormalization_scale_ne_zero σ z)] at hh
    exact σ.injective (z.property.1 (sub_left_inj.mp hh))
  · simp [renormalizedPositions]
  · rw [renormalizedPositions, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    exact div_self (Complex.ofReal_ne_zero.mp (renormalization_scale_ne_zero σ z))

/-- The holomorphic shape transition is exactly the coordinate change induced
by renormalizing the actual original planar array. -/
theorem shape_renormalize {N : ℕ} (σ : Equiv.Perm (Point N)) (z : Normalized N) :
    shape (renormalize σ z) = referenceChange σ (shape z) := by
  funext j
  change ((z.val (σ j.succ.succ) - z.val (σ 0)) / (‖z.val (σ 1) - z.val (σ 0)‖ : ℂ)) /
      ((z.val (σ 1) - z.val (σ 0)) / (‖z.val (σ 1) - z.val (σ 0)‖ : ℂ)) = _
  rw [div_div_div_cancel_right₀ (renormalization_scale_ne_zero σ z), referenceChange,
    normalizedPoint_shape, normalizedPoint_shape, normalizedPoint_shape,
    ← sub_div, ← sub_div, div_div_div_cancel_right₀ (reference_ne_zero z)]

theorem continuous_renormalize {N : ℕ} (σ : Equiv.Perm (Point N)) : Continuous (renormalize σ) := by
  have h (j : Point N) : Continuous (fun z : Normalized N ↦ z.val (σ j)) :=
    (continuous_apply (σ j)).comp continuous_subtype_val
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  change Continuous (fun z : Normalized N ↦ renormalizedPositions σ z j)
  exact ((h j).sub (h 0)).div
    (Complex.ofRealCLM.continuous.comp ((h 1).sub (h 0)).norm)
    (fun z ↦ renormalization_scale_ne_zero σ z)

end EnvelopingIsomorphism.Deformation.Kontsevich.PlanarNormalizedCoordinates
