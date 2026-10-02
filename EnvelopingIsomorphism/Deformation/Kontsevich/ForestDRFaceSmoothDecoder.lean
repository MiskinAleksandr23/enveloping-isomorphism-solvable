import EnvelopingIsomorphism.Deformation.Kontsevich.ForestDRInverse
import EnvelopingIsomorphism.Deformation.Kontsevich.CompactDRCoordinates

/-! Smooth ambient formulas for the native DR decoder on a fixed radius-zero
stratum. Selected radii are fixed to zero; no norm is differentiated at zero.
All other entries use the literal marked decoder formulas. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestDRFaceSmoothDecoder
open ForestDirectionRatioCoordinates ForestMarkedFrames ForestDRParameterIdentification
open scoped Classical ContDiff

abbrev Ambient (I : Type*) := (Pair I → ℂ) × (Triple I → ℝ)

def embed {I : Type*} (d : Data I) : Ambient I :=
  (fun e ↦ (d.1 e : ℂ), fun e ↦ (d.2 e : ℝ))

variable {I : Type*} [Fintype I] [DecidableEq I]

def recoverArray (a b : I) (hab : a ≠ b) (x : Ambient I) (j : I) : ℂ :=
  if hja : j = a then 0 else
    (x.2 (MarkedDRIdentification.markedTriple a j b (Ne.symm hja) hab) /
      (1 - x.2 (MarkedDRIdentification.markedTriple a j b (Ne.symm hja) hab)) : ℝ) *
      x.1 (MarkedDRIdentification.markedPair a j (Ne.symm hja))

@[simp] theorem recoverArray_embed (a b : I) (hab : a ≠ b) (d : Data I) :
    recoverArray a b hab (embed d) = MarkedDRIdentification.recoverArray a b hab d := by
  funext j
  simp only [recoverArray, MarkedDRIdentification.recoverArray]
  split_ifs <;> rfl

theorem contDiffAt_recoverArray (a b : I) (hab : a ≠ b) (j : I) (x : Ambient I)
    (hfinite : ∀ hja : j ≠ a, x.2 (MarkedDRIdentification.markedTriple a j b (Ne.symm hja) hab) < 1) :
    ContDiffAt ℝ ⊤ (fun d ↦ recoverArray a b hab d j) x := by
  unfold recoverArray
  split_ifs with hja
  · exact contDiffAt_const
  · apply ContDiffAt.mul
    · apply Complex.ofRealCLM.contDiff.contDiffAt.comp x
      exact (by fun_prop : ContDiffAt ℝ ⊤ (fun d : Ambient I ↦
        d.2 (MarkedDRIdentification.markedTriple a j b (Ne.symm hja) hab)) x).div
        (by fun_prop) (sub_ne_zero.mpr (hfinite hja).ne')
    · fun_prop

variable (T : RootedTree) [Fintype T] (lab : T → I)

def corrected (d : Reference I) (x : Ambient I) (j : I) : ℂ :=
  recoverArray d.a d.b d.ne x j - match d.correction with
    | none => 0
    | some c => recoverArray d.a d.b d.ne x c / 2

def recoveredArray (A : T) (d : Reference I) (x : Ambient I) : T → ℂ :=
  fun v ↦ if A ≤ v ∧ IsMax v then corrected d x (lab v) else 0

@[simp] theorem recoveredArray_embed (A : T) (d : Reference I) (x : Data I) :
    recoveredArray T lab A d (embed x) = ForestDRParameterIdentification.recoveredArray T lab A d x := by
  funext v
  simp only [recoveredArray, ForestDRParameterIdentification.recoveredArray]
  split_ifs
  · simp only [corrected, Reference.corrected, recoverArray_embed]
    rfl
  · rfl

theorem contDiffAt_recoveredArray (A : T) (d : Reference I) (x : Data I)
    (hx : x ∈ ForestDRParameterIdentification.FiniteRegion T lab A d) :
    ContDiffAt ℝ ⊤ (recoveredArray T lab A d) (embed x) := by
  apply contDiffAt_pi.mpr
  intro v
  by_cases hv : A ≤ v ∧ IsMax v
  · simp only [recoveredArray, if_pos hv, corrected]
    apply ContDiffAt.sub
    · exact contDiffAt_recoverArray d.a d.b d.ne (lab v) _
        (hx ⟨lab v, leaf_mem_outputs T lab A d v hv.1 hv.2⟩)
    · cases hc : d.correction with
      | none => exact contDiffAt_const
      | some c => exact (contDiffAt_recoverArray d.a d.b d.ne c _
          (hx ⟨c, correction_mem_outputs T lab A d c hc⟩)).div_const 2
  · simp only [recoveredArray, if_neg hv]
    exact contDiffAt_const

/-- Only the one radius being differentiated must have a positive marked gap. -/
theorem contDiffAt_radius_of_pos (F : Frames T) (q : T → ℂ) (v : T)
    (h : 0 < radius T F q v) : ContDiffAt ℝ ⊤ (fun p ↦ radius T F p v) q := by
  by_cases hv : IsMax v
  · simp only [radius, dif_pos hv]
    exact contDiffAt_const
  · simp only [radius, dif_neg hv] at h ⊢
    exact ((F v hv).contDiffAt_radius (centers T F q) h).comp q (contDiff_centers T F).contDiffAt

def childIncrement (F : Frames T) (A B : T) (d : Reference I) (x : Ambient I) : ℂ :=
  ForestMarkedFrames.normalized T F (recoveredArray T lab A d x) A B

def childRadius (F : Frames T) (A B : T) (d : Reference I) (x : Ambient I) : ℝ :=
  radius T F (recoveredArray T lab A d x) B / radius T F (recoveredArray T lab A d x) A

@[simp] theorem childIncrement_embed (F : Frames T) (A B : T) (d : Reference I) (x : Data I) :
    childIncrement T lab F A B d (embed x) = ForestDRParameterIdentification.childIncrement T lab F A B d x := by
  simp only [childIncrement, ForestDRParameterIdentification.childIncrement, recoveredArray_embed]

@[simp] theorem childRadius_embed (F : Frames T) (A B : T) (d : Reference I) (x : Data I) :
    childRadius T lab F A B d (embed x) = ForestDRParameterIdentification.childRadius T lab F A B d x := by
  simp only [childRadius, ForestDRParameterIdentification.childRadius, recoveredArray_embed]

theorem contDiffAt_childIncrement (F : Frames T) (A B : T) (d : Reference I) (x : Data I)
    (hx : x ∈ ForestDRParameterIdentification.Region T lab F A d) :
    ContDiffAt ℝ ⊤ (childIncrement T lab F A B d) (embed x) := by
  have ha := contDiffAt_recoveredArray T lab A d x hx.1
  have hp : 0 < radius T F (recoveredArray T lab A d (embed x)) A := by
    simpa only [recoveredArray_embed, Set.mem_setOf_eq] using hx.2
  have hr := (contDiffAt_radius_of_pos T F _ A hp).comp (embed x) ha
  have hc := ((center T F B).contDiff.contDiffAt.comp (embed x) ha).sub
    ((center T F A).contDiff.contDiffAt.comp (embed x) ha)
  change ContDiffAt ℝ ⊤ (fun y : Ambient I ↦
    (center T F B (recoveredArray T lab A d y) - center T F A (recoveredArray T lab A d y)) /
      (radius T F (recoveredArray T lab A d y) A : ℂ)) (embed x)
  simpa only [div_eq_mul_inv, Pi.inv_apply, Function.comp_def, Complex.ofRealCLM_apply] using
    hc.mul ((Complex.ofRealCLM.contDiff.contDiffAt.comp (embed x) hr).inv
      (Complex.ofReal_ne_zero.mpr hp.ne'))

theorem contDiffAt_childRadius (F : Frames T) (A B : T) (d : Reference I) (x : Data I)
    (hx : x ∈ ForestDRParameterIdentification.Region T lab F A d)
    (hB : 0 < ForestDRParameterIdentification.childRadius T lab F A B d x) :
    ContDiffAt ℝ ⊤ (childRadius T lab F A B d) (embed x) := by
  have ha := contDiffAt_recoveredArray T lab A d x hx.1
  have hp : 0 < radius T F (recoveredArray T lab A d (embed x)) A := by
    simpa only [recoveredArray_embed, Set.mem_setOf_eq] using hx.2
  have hB' : 0 < radius T F (recoveredArray T lab A d (embed x)) B := by
    rw [recoveredArray_embed]
    exact (div_pos_iff_of_pos_right hx.2).mp hB
  exact ((contDiffAt_radius_of_pos T F _ B hB').comp (embed x) ha).div
    ((contDiffAt_radius_of_pos T F _ A hp).comp (embed x) ha) hp.ne'

variable (F : Frames T) (d : ForestDRInverse.References T (I := I)) (Z : Set T)

def radii (x : Ambient I) : T → ℝ := fun B ↦
  if IsMax B then 1 else if hB : B = ⊥ then 1 else
    if B ∈ Z then 0 else childRadius T lab F (Order.pred B) B
      (d (Order.pred B) (ForestDRInverse.pred_internal T B hB)) x

def increments (x : Ambient I) : T → ℂ := fun B ↦
  if hB : B = ⊥ then 0 else childIncrement T lab F (Order.pred B) B
    (d (Order.pred B) (ForestDRInverse.pred_internal T B hB)) x

def decode (x : Ambient I) : Parameters T := (radii T lab F d Z x, increments T lab F d x)

/-- Exact restriction of the native decoder to its specified zero-radius stratum. -/
theorem decode_embed (x : Data I)
    (hZ : ∀ B ∈ Z, (ForestDRInverse.decode T lab F d x).1 B = 0) :
    decode T lab F d Z (embed x) = ForestDRInverse.decode T lab F d x := by
  apply Prod.ext
  · funext B
    simp only [decode, radii, ForestDRInverse.decode, ForestDRInverse.recoveredRadii]
    split_ifs with hmax hroot hzero
    · rfl
    · rfl
    · simpa only [ForestDRInverse.decode, ForestDRInverse.recoveredRadii, if_neg hmax, dif_neg hroot] using (hZ B hzero).symm
    · exact childRadius_embed T lab F _ _ _ x
  · funext B
    simp only [decode, increments, ForestDRInverse.decode, ForestDRInverse.recoveredIncrements]
    split_ifs
    · rfl
    · exact childIncrement_embed T lab F _ _ _ x

/-- Smoothness is proved directly from the actual finite scalar formulas;
only the genuinely nonzero radii are differentiated. -/
theorem contDiffAt_decode (x : Data I) (hx : x ∈ ForestDRInverse.Region T lab F d)
    (hpos : ∀ B, ¬ IsMax B → B ≠ ⊥ → B ∉ Z → 0 < (ForestDRInverse.decode T lab F d x).1 B) :
    ContDiffAt ℝ ⊤ (decode T lab F d Z) (embed x) := by
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro B
    simp only [radii]
    split_ifs with hmax hroot hzero
    · exact contDiffAt_const
    · exact contDiffAt_const
    · exact contDiffAt_const
    · apply contDiffAt_childRadius T lab F _ _ _ x (hx _ _)
      simpa only [ForestDRInverse.decode, ForestDRInverse.recoveredRadii,
        if_neg hmax, dif_neg hroot] using hpos B hmax hroot hzero
  · apply contDiffAt_pi.mpr
    intro B
    simp only [increments]
    split_ifs
    · exact contDiffAt_const
    · exact contDiffAt_childIncrement T lab F _ _ _ x (hx _ _)

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestDRFaceSmoothDecoder
