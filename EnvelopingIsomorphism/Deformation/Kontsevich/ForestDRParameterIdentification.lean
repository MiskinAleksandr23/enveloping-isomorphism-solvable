import EnvelopingIsomorphism.Deformation.Kontsevich.ForestMarkedFrameInverse
import EnvelopingIsomorphism.Deformation.Kontsevich.MarkedDRIdentification

/-! Local continuous identification of marked forest parameters from stored DR data.
Only descendant leaves are read. Stable charts use the reflected reference to
correct the translation to a real translation. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestDRParameterIdentification

open ForestMarkedFrames ForestDirectionRatioCoordinates MarkedDRIdentification
open scoped Classical

variable (T : RootedTree) [Fintype T]

/-- A complex translation is allowed precisely where the recursive frames are
complex. Real translations work through every frame type. -/
def CompatibleShift (F : Frames T) (A : T) (z : ℂ) : Prop :=
  ∀ v (hv : ¬ IsMax v), A ≤ v → match F v hv with
    | .complex _ _ _ _ _ => True
    | .stableHeight _ _ => z.im = 0
    | .stableRealPair _ _ _ _ _ => z.im = 0

omit [Fintype T] in
theorem compatibleShift_real (F : Frames T) (A : T) (z : ℝ) :
    CompatibleShift T F A (z : ℂ) := by
  intro v hv hAv
  cases F v hv <;> simp

private theorem realPart_affine (u z : ℂ) (R : ℝ) (hz : z.im = 0) :
    (((u - z) / (R : ℂ)).re : ℂ) = (((u.re : ℂ) - z) / (R : ℂ)) := by
  apply Complex.ext <;> simp [hz]

/-- Covariance follows from the actual finite recursion, and needs input
agreement only at the descendant leaves. -/
theorem center_affine_subtree (F : Frames T) (A : T) (p q : T → ℂ) (z : ℂ) (R : ℝ)
    (hz : CompatibleShift T F A z)
    (hq : ∀ v, A ≤ v → IsMax v → q v = (p v - z) / (R : ℂ))
    (v : T) (hAv : A ≤ v) :
    center T F v q = (center T F v p - z) / (R : ℂ) := by
  induction v using WellFoundedGT.induction with
  | ind v ih =>
    by_cases hv : IsMax v
    · rw [center_leaf T F v hv, center_leaf T F v hv, hq v hAv hv]
    · have hshift := hz v hv hAv
      cases hf : F v hv with
      | complex b c hb hc hne =>
        rw [center_complex T F v b c hv hb hc hne hf]
        exact ih b hb.lt (hAv.trans hb.le)
      | stableHeight b hb =>
        rw [hf] at hshift
        rw [center_stableHeight T F v b hv hb hf, center_stableHeight T F v b hv hb hf,
          ih b hb.lt (hAv.trans hb.le), realPart_affine _ _ _ hshift]
      | stableRealPair b c hb hc hne =>
        rw [hf] at hshift
        rw [center_stableRealPair T F v b c hv hb hc hne hf,
          center_stableRealPair T F v b c hv hb hc hne hf,
          ih b hb.lt (hAv.trans hb.le), realPart_affine _ _ _ hshift]

theorem radius_affine_subtree (F : Frames T) (A : T) (p q : T → ℂ) (z : ℂ) (R : ℝ)
    (hR : 0 < R) (hz : CompatibleShift T F A z)
    (hq : ∀ v, A ≤ v → IsMax v → q v = (p v - z) / (R : ℂ))
    (v : T) (hAv : A ≤ v) (hv : ¬ IsMax v) :
    radius T F q v = radius T F p v / R := by
  rw [radius_nonleaf T F q v hv, radius_nonleaf T F p v hv]
  have hshift := hz v hv hAv
  cases hf : F v hv with
  | complex b c hb hc hne =>
    change ‖center T F c q - center T F b q‖ = ‖center T F c p - center T F b p‖ / R
    rw [center_affine_subtree T F A p q z R hz hq c (hAv.trans hc.le),
      center_affine_subtree T F A p q z R hz hq b (hAv.trans hb.le), ← sub_div]
    have he : (center T F c p - z) - (center T F b p - z) =
        center T F c p - center T F b p := by abel
    rw [he, norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le]
  | stableHeight b hb =>
    rw [hf] at hshift
    change (center T F b q).im = (center T F b p).im / R
    rw [center_affine_subtree T F A p q z R hz hq b (hAv.trans hb.le)]
    simp [hshift]
  | stableRealPair b c hb hc hne =>
    change (center T F c q).re - (center T F b q).re =
      ((center T F c p).re - (center T F b p).re) / R
    rw [center_affine_subtree T F A p q z R hz hq c (hAv.trans hc.le),
      center_affine_subtree T F A p q z R hz hq b (hAv.trans hb.le)]
    simp only [Complex.div_ofReal_re, Complex.sub_re]
    ring

/-- Original reference labels; `some c` means the stable correction using the
reflected anchor label `c = σ a`. -/
structure Reference (I : Type*) where
  a : I
  b : I
  ne : a ≠ b
  correction : Option I

namespace Reference

variable {I : Type*}

def corrected (d : Reference I) (x : Data I) (j : I) : ℂ :=
  recoverArray d.a d.b d.ne x j -
    match d.correction with
    | none => 0
    | some c => recoverArray d.a d.b d.ne x c / 2

def shift (d : Reference I) (p : I → ℂ) : ℂ :=
  match d.correction with
  | none => p d.a
  | some c => (p d.a + p c) / 2

theorem corrected_ofPositions (d : Reference I) (p : I → ℂ) (href : p d.a ≠ p d.b)
    (j : I) : corrected d (ofPositions p) j =
      (p j - d.shift p) / (‖p d.b - p d.a‖ : ℂ) := by
  unfold corrected shift
  cases hc : d.correction with
  | none => simp [recoverArray_ofPositions p d.a d.b d.ne href]
  | some c =>
    dsimp only
    rw [recoverArray_ofPositions p d.a d.b d.ne href j,
      recoverArray_ofPositions p d.a d.b d.ne href c]
    ring

theorem shift_stable (d : Reference I) (p : I → ℂ) (c : I) (hc : d.correction = some c)
    (hp : p c = star (p d.a)) : d.shift p = ((p d.a).re : ℂ) := by
  simp only [shift, hc, hp]
  apply Complex.ext <;> simp

theorem corrected_stable_ofPositions (d : Reference I) (p : I → ℂ)
    (href : p d.a ≠ p d.b) (c : I) (hc : d.correction = some c)
    (hp : p c = star (p d.a)) (j : I) :
    corrected d (ofPositions p) j = (p j - ((p d.a).re : ℂ)) / (‖p d.b - p d.a‖ : ℂ) := by
  rw [corrected_ofPositions d p href j, shift_stable d p c hc hp]

end Reference

variable {I : Type*} (lab : T → I)

def outputs (A : T) (d : Reference I) : Finset I :=
  ((Finset.univ.filter fun v : T => A ≤ v ∧ IsMax v).image lab) ∪ d.correction.toFinset

theorem leaf_mem_outputs (A : T) (d : Reference I) (v : T) (hAv : A ≤ v) (hv : IsMax v) :
    lab v ∈ outputs T lab A d := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨v, by simp [hAv, hv], rfl⟩

theorem correction_mem_outputs (A : T) (d : Reference I) (c : I)
    (hc : d.correction = some c) : c ∈ outputs T lab A d := by
  simp [outputs, hc]

/-- Extension by zero outside the descendant leaves. Recursive centers in the
subtree depend only on the entries retained here. -/
def recoveredArray (A : T) (d : Reference I) (x : Data I) : T → ℂ :=
  fun v => if A ≤ v ∧ IsMax v then d.corrected x (lab v) else 0

def FiniteRegion (A : T) (d : Reference I) : Set (Data I) :=
  MarkedDRIdentification.FiniteRegion (outputs T lab A d) d.a d.b d.ne

theorem isOpen_finiteRegion (A : T) (d : Reference I) : IsOpen (FiniteRegion T lab A d) :=
  MarkedDRIdentification.isOpen_finiteRegion _ _ _ _

theorem continuousAt_recoveredArray (A : T) (d : Reference I) (x : Data I)
    (hx : x ∈ FiniteRegion T lab A d) : ContinuousAt (recoveredArray T lab A d) x := by
  apply continuousAt_pi.mpr
  intro v
  by_cases hv : A ≤ v ∧ IsMax v
  · simp only [recoveredArray, if_pos hv, Reference.corrected]
    apply ContinuousAt.sub
    · exact continuousAt_recoverArray d.a d.b d.ne (lab v) x
        (hx ⟨lab v, leaf_mem_outputs T lab A d v hv.1 hv.2⟩)
    · cases hc : d.correction with
      | none => exact continuousAt_const
      | some c =>
        exact (continuousAt_recoverArray d.a d.b d.ne c x
          (hx ⟨c, correction_mem_outputs T lab A d c hc⟩)).div_const 2
  · simp only [recoveredArray, if_neg hv]
    exact continuousAt_const

def Region (F : Frames T) (A : T) (d : Reference I) : Set (Data I) :=
  FiniteRegion T lab A d ∩ {x | 0 < radius T F (recoveredArray T lab A d x) A}

theorem isOpen_region (F : Frames T) (A : T) (d : Reference I) :
    IsOpen (Region T lab F A d) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  apply Filter.inter_mem ((isOpen_finiteRegion T lab A d).mem_nhds hx.1)
  exact ((continuous_radius T F A).continuousAt.comp
    (continuousAt_recoveredArray T lab A d x hx.1)).preimage_mem_nhds
      (IsOpen.mem_nhds isOpen_Ioi hx.2)

/-- Parent-normalized child center displacement, read from stored DR data. -/
def childIncrement (F : Frames T) (A B : T) (d : Reference I) (x : Data I) : ℂ :=
  normalized T F (recoveredArray T lab A d x) A B

/-- The numerator is allowed to vanish at a corner. Only the parent marked
radius is required positive. -/
def childRadius (F : Frames T) (A B : T) (d : Reference I) (x : Data I) : ℝ :=
  radius T F (recoveredArray T lab A d x) B / radius T F (recoveredArray T lab A d x) A

theorem continuousAt_childIncrement (F : Frames T) (A B : T) (d : Reference I)
    (x : Data I) (hx : x ∈ Region T lab F A d) :
    ContinuousAt (childIncrement T lab F A B d) x := by
  have hq := continuousAt_recoveredArray T lab A d x hx.1
  exact (((center T F B).continuous.continuousAt.comp hq).sub
    ((center T F A).continuous.continuousAt.comp hq)).div
    (Complex.continuous_ofReal.continuousAt.comp ((continuous_radius T F A).continuousAt.comp hq))
    (Complex.ofReal_ne_zero.mpr hx.2.ne')

theorem continuousAt_childRadius (F : Frames T) (A B : T) (d : Reference I)
    (x : Data I) (hx : x ∈ Region T lab F A d) :
    ContinuousAt (childRadius T lab F A B d) x := by
  have hq := continuousAt_recoveredArray T lab A d x hx.1
  exact ((continuous_radius T F B).continuousAt.comp hq).div
    ((continuous_radius T F A).continuousAt.comp hq) hx.2.ne'

theorem continuousOn_childIncrement (F : Frames T) (A B : T) (d : Reference I) :
    ContinuousOn (childIncrement T lab F A B d) (Region T lab F A d) :=
  fun x hx => (continuousAt_childIncrement T lab F A B d x hx).continuousWithinAt

theorem continuousOn_childRadius (F : Frames T) (A B : T) (d : Reference I) :
    ContinuousOn (childRadius T lab F A B d) (Region T lab F A d) :=
  fun x hx => (continuousAt_childRadius T lab F A B d x hx).continuousWithinAt

theorem center_recovered_ofPositions (F : Frames T) (A : T) (d : Reference I)
    (p : I → ℂ) (P : T → ℂ) (href : p d.a ≠ p d.b)
    (hp : ∀ v, A ≤ v → IsMax v → p (lab v) = P v)
    (hz : CompatibleShift T F A (d.shift p)) (v : T) (hAv : A ≤ v) :
    center T F v (recoveredArray T lab A d (ofPositions p)) =
      (center T F v P - d.shift p) / (‖p d.b - p d.a‖ : ℂ) := by
  apply center_affine_subtree T F A P _ _ _ hz _ v hAv
  intro w hAw hw
  simp only [recoveredArray, if_pos (show A ≤ w ∧ IsMax w from ⟨hAw, hw⟩), Reference.corrected_ofPositions d p href,
    hp w hAw hw]

theorem radius_recovered_ofPositions (F : Frames T) (A : T) (d : Reference I)
    (p : I → ℂ) (P : T → ℂ) (href : p d.a ≠ p d.b)
    (hp : ∀ v, A ≤ v → IsMax v → p (lab v) = P v)
    (hz : CompatibleShift T F A (d.shift p)) (v : T) (hAv : A ≤ v) (hv : ¬ IsMax v) :
    radius T F (recoveredArray T lab A d (ofPositions p)) v =
      radius T F P v / ‖p d.b - p d.a‖ := by
  apply radius_affine_subtree T F A P _ _ _
    (norm_pos_iff.mpr (sub_ne_zero.mpr href.symm)) hz _ v hAv hv
  intro w hAw hw
  simp only [recoveredArray, if_pos (show A ≤ w ∧ IsMax w from ⟨hAw, hw⟩), Reference.corrected_ofPositions d p href,
    hp w hAw hw]

theorem ofPositions_mem_region (F : Frames T) (A : T) (d : Reference I)
    (p : I → ℂ) (P : T → ℂ) (href : p d.a ≠ p d.b)
    (hp : ∀ v, A ≤ v → IsMax v → p (lab v) = P v)
    (hz : CompatibleShift T F A (d.shift p)) (hA : ¬ IsMax A) (hpos : 0 < radius T F P A) :
    ofPositions p ∈ Region T lab F A d := by
  refine ⟨ofPositions_mem_finiteRegion _ p d.a d.b d.ne href, ?_⟩
  change 0 < radius T F (recoveredArray T lab A d (ofPositions p)) A
  rw [radius_recovered_ofPositions T lab F A d p P href hp hz A le_rfl hA]
  exact div_pos hpos (norm_pos_iff.mpr (sub_ne_zero.mpr href.symm))

/-- Exact original-coordinate increment identification. No equality of recovered
parameters is supplied as a hypothesis. -/
theorem childIncrement_ofPositions (F : Frames T) (A B : T) (d : Reference I)
    (p : I → ℂ) (P : T → ℂ) (href : p d.a ≠ p d.b)
    (hp : ∀ v, A ≤ v → IsMax v → p (lab v) = P v)
    (hz : CompatibleShift T F A (d.shift p)) (hA : ¬ IsMax A) (hAB : A ≤ B) :
    childIncrement T lab F A B d (ofPositions p) = normalized T F P A B := by
  unfold childIncrement normalized
  rw [center_recovered_ofPositions T lab F A d p P href hp hz B hAB,
    center_recovered_ofPositions T lab F A d p P href hp hz A le_rfl,
    radius_recovered_ofPositions T lab F A d p P href hp hz A le_rfl hA,
    Complex.ofReal_div, ← sub_div]
  have he : (center T F B P - d.shift p) - (center T F A P - d.shift p) =
      center T F B P - center T F A P := by abel
  rw [he, div_div_div_cancel_right₀]
  exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (sub_ne_zero.mpr href.symm))

/-- Exact original-coordinate internal radius ratio, including zero child
radius. Both nodes must be internal because leaf radii are dummy values. -/
theorem childRadius_ofPositions (F : Frames T) (A B : T) (d : Reference I)
    (p : I → ℂ) (P : T → ℂ) (href : p d.a ≠ p d.b)
    (hp : ∀ v, A ≤ v → IsMax v → p (lab v) = P v)
    (hz : CompatibleShift T F A (d.shift p)) (hA : ¬ IsMax A) (hAB : A ≤ B)
    (hB : ¬ IsMax B) : childRadius T lab F A B d (ofPositions p) = radius T F P B / radius T F P A := by
  unfold childRadius
  rw [radius_recovered_ofPositions T lab F A d p P href hp hz B hAB hB,
    radius_recovered_ofPositions T lab F A d p P href hp hz A le_rfl hA,
    div_div_div_cancel_right₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr href.symm))]

omit [Fintype T] in
/-- Stable reflected-reference charts automatically satisfy the translation
condition for the recursive factory, regardless of descendant frame types. -/
theorem compatibleShift_stable (F : Frames T) (A : T) (d : Reference I)
    (p : I → ℂ) (c : I) (hc : d.correction = some c) (hp : p c = star (p d.a)) :
    CompatibleShift T F A (d.shift p) := by
  rw [Reference.shift_stable d p c hc hp]
  exact compatibleShift_real T F A _

/-- In a nonstable subtree every internal frame is complex. This explicit
geometric input permits its complex reference translation. -/
def ComplexSubtree (F : Frames T) (A : T) : Prop :=
  ∀ v (hv : ¬ IsMax v), A ≤ v → ∃ b c hb hc hne, F v hv = .complex b c hb hc hne

omit [Fintype T] in
theorem compatibleShift_complexSubtree (F : Frames T) (A : T)
    (hF : ComplexSubtree T F A) (z : ℂ) : CompatibleShift T F A z := by
  intro v hv hAv
  obtain ⟨b, c, hb, hc, hne, hf⟩ := hF v hv hAv
  simp [hf]

open ForestMarkedFrameInverse ForestInsertionDifference AncestorScaleRatios ForestNormalizationTelescope

/-- Composition with actual original leaf insertion recovers the original
child increment, by the proved recursive positional inverse. -/
theorem childIncrement_inserted (F : Frames T) (A B : T) (d : Reference I)
    (p : I → ℂ) (r : T → ℝ) (a : T → ℂ) (href : p d.a ≠ p d.b)
    (hp : ∀ v, A ≤ v → IsMax v → p (lab v) = position T r a v)
    (hz : CompatibleShift T F A (d.shift p)) (hAB : A ⋖ B)
    (hr : PositiveInternal T r) (ha : ForestMarkedFrameInverse.Normalized T F r a) :
    childIncrement T lab F A B d (ofPositions p) = a B := by
  rw [childIncrement_ofPositions T lab F A B d p (position T r a) href hp hz
    (not_isMax_of_lt hAB.lt) hAB.le]
  exact normalized_child_position T F r a hr ha A B hAB

/-- Original internal local radius, recovered from stored original DR data.
This proof does not posit any marked-center or marked-radius identification law. -/
theorem childRadius_inserted (F : Frames T) (A B : T) (d : Reference I)
    (p : I → ℂ) (r : T → ℝ) (a : T → ℂ) (href : p d.a ≠ p d.b)
    (hp : ∀ v, A ≤ v → IsMax v → p (lab v) = position T r a v)
    (hz : CompatibleShift T F A (d.shift p)) (hAB : A ⋖ B) (hB : ¬ IsMax B)
    (hr : PositiveInternal T r) (ha : ForestMarkedFrameInverse.Normalized T F r a) :
    childRadius T lab F A B d (ofPositions p) = r B := by
  have hA := not_isMax_of_lt hAB.lt
  rw [childRadius_ofPositions T lab F A B d p (position T r a) href hp hz hA hAB.le hB,
    radius_position T F r a hr ha B hB, radius_position T F r a hr ha A hA,
    scale_step T r B (ne_bot_of_gt hAB.lt), hAB.pred_eq,
    mul_div_cancel_right₀ _ (scale_pos_internal T r hr A hA).ne']

theorem inserted_mem_region (F : Frames T) (A B : T) (d : Reference I)
    (p : I → ℂ) (r : T → ℝ) (a : T → ℂ) (href : p d.a ≠ p d.b)
    (hp : ∀ v, A ≤ v → IsMax v → p (lab v) = position T r a v)
    (hz : CompatibleShift T F A (d.shift p)) (hAB : A ⋖ B)
    (hr : PositiveInternal T r) (ha : ForestMarkedFrameInverse.Normalized T F r a) :
    ofPositions p ∈ Region T lab F A d := by
  apply ofPositions_mem_region T lab F A d p (position T r a) href hp hz
    (not_isMax_of_lt hAB.lt)
  exact positiveGaps_position T F r a hr ha A

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestDRParameterIdentification
