import EnvelopingIsomorphism.Deformation.Kontsevich.ForestNormalizationTelescope
import EnvelopingIsomorphism.Deformation.Kontsevich.MarkedClusterSmooth

/-! Actual marked frames on a finite native rooted tree. Centers recurse towards
leaves, and are continuous real-linear functions of the leaf/node positions.
Positive gaps are conditions on these actual centers. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestMarkedFrames

open scoped Classical ContDiff

variable (T : RootedTree) [Fintype T]

/-- Marks are immediate children, never arbitrary descendants. -/
inductive Frame (v : T) where
  | complex (a b : T) (ha : v ⋖ a) (hb : v ⋖ b) (hne : a ≠ b)
  | stableHeight (a : T) (ha : v ⋖ a)
  | stableRealPair (a b : T) (ha : v ⋖ a) (hb : v ⋖ b) (hne : a ≠ b)

/-- Only nonleaves require a frame. -/
abbrev Frames := (v : T) → ¬ IsMax v → Frame T v

def realPart : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM

@[simp] theorem realPart_apply (z : ℂ) : realPart z = (z.re : ℂ) := rfl

def centerStep (F : Frames T) (v : T)
    (rec : (w : T) → v < w → ((T → ℂ) →L[ℝ] ℂ)) : (T → ℂ) →L[ℝ] ℂ :=
  if hv : IsMax v then ContinuousLinearMap.proj v else
    match F v hv with
    | .complex a _ ha _ _ => rec a ha.lt
    | .stableHeight a ha => realPart.comp (rec a ha.lt)
    | .stableRealPair a _ ha _ _ => realPart.comp (rec a ha.lt)

/-- Finite upward well-founded recursion: at each nonleaf only a strict child
is used. This is a construction, with no assumed center equations. -/
def center (F : Frames T) : T → ((T → ℂ) →L[ℝ] ℂ) :=
  (Finite.to_wellFoundedGT (α := T)).wf.fix (centerStep T F)

theorem center_eq (F : Frames T) (v : T) :
    center T F v = centerStep T F v (fun w _ => center T F w) :=
  WellFounded.fix_eq _ _ _

@[simp] theorem center_leaf (F : Frames T) (v : T) (hv : IsMax v) (p : T → ℂ) :
    center T F v p = p v := by
  rw [center_eq]
  simp [centerStep, hv]

theorem center_complex (F : Frames T) (v a b : T) (hv : ¬ IsMax v)
    (ha : v ⋖ a) (hb : v ⋖ b) (hne : a ≠ b)
    (hf : F v hv = .complex a b ha hb hne) : center T F v = center T F a := by
  rw [center_eq]
  simp [centerStep, hv, hf]

theorem center_stableHeight (F : Frames T) (v a : T) (hv : ¬ IsMax v)
    (ha : v ⋖ a) (hf : F v hv = .stableHeight a ha) (p : T → ℂ) :
    center T F v p = ((center T F a p).re : ℂ) := by
  rw [center_eq]
  simp [centerStep, hv, hf]

theorem center_stableRealPair (F : Frames T) (v a b : T) (hv : ¬ IsMax v)
    (ha : v ⋖ a) (hb : v ⋖ b) (hne : a ≠ b)
    (hf : F v hv = .stableRealPair a b ha hb hne) (p : T → ℂ) :
    center T F v p = ((center T F a p).re : ℂ) := by
  rw [center_eq]
  simp [centerStep, hv, hf]

def centers (F : Frames T) : (T → ℂ) →L[ℝ] (T → ℂ) :=
  ContinuousLinearMap.pi (center T F)

@[simp] theorem centers_apply (F : Frames T) (p : T → ℂ) (v : T) :
    centers T F p v = center T F v p := rfl

variable {ν : ℕ∞ω}

@[fun_prop] theorem contDiff_center (F : Frames T) (v : T) :
    ContDiff ℝ ν (center T F v) := (center T F v).contDiff

@[fun_prop] theorem contDiff_centers (F : Frames T) :
    ContDiff ℝ ν (centers T F) := (centers T F).contDiff

namespace Frame

open MarkedClusterRescaling

variable {T} {v : T}

def radius (f : Frame T v) (q : T → ℂ) : ℝ :=
  match f with
  | .complex a b _ _ _ => pairRadius a b q
  | .stableHeight a _ => heightRadius a q
  | .stableRealPair a b _ _ _ => orderedRealRadius a b q

def base (f : Frame T v) (q : T → ℂ) : ℂ :=
  match f with
  | .complex a _ _ _ _ => q a
  | .stableHeight a _ => (q a).re
  | .stableRealPair a _ _ _ _ => (q a).re

def normalized (f : Frame T v) (q : T → ℂ) (w : T) : ℂ :=
  (q w - f.base q) / (f.radius q : ℂ)

@[fun_prop] theorem contDiff_base (f : Frame T v) : ContDiff ℝ ν f.base := by
  cases f with
  | complex a b ha hb hne => exact (ContinuousLinearMap.proj a : (T → ℂ) →L[ℝ] ℂ).contDiff
  | stableHeight a ha =>
    exact (realPart.comp (ContinuousLinearMap.proj a : (T → ℂ) →L[ℝ] ℂ)).contDiff
  | stableRealPair a b ha hb hne =>
    exact (realPart.comp (ContinuousLinearMap.proj a : (T → ℂ) →L[ℝ] ℂ)).contDiff

omit [Fintype T] in
theorem continuous_radius (f : Frame T v) : Continuous f.radius := by
  cases f <;> unfold radius pairRadius heightRadius orderedRealRadius <;> fun_prop

theorem contDiffAt_radius (f : Frame T v) (q : T → ℂ) (hq : 0 < f.radius q) :
    ContDiffAt ℝ ν f.radius q := by
  cases f with
  | complex a b ha hb hne =>
    apply contDiffAt_pairRadius
    intro hab
    simp [radius, pairRadius, hab] at hq
  | stableHeight a ha => exact (contDiff_heightRadius a).contDiffAt
  | stableRealPair a b ha hb hne => exact (contDiff_orderedRealRadius a b).contDiffAt

theorem contDiffAt_normalized (f : Frame T v) (q : T → ℂ) (hq : 0 < f.radius q) :
    ContDiffAt ℝ ν f.normalized q := by
  apply contDiffAt_pi.mpr
  intro w
  simp only [normalized, div_eq_mul_inv]
  apply ContDiffAt.mul
  · exact (show ContDiffAt ℝ ν (fun p : T → ℂ => p w) q by fun_prop).sub
      f.contDiff_base.contDiffAt
  · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp q
      (f.contDiffAt_radius q hq)).inv (Complex.ofReal_ne_zero.mpr hq.ne')

omit [Fintype T] in
theorem complex_zero (a b : T) (ha : v ⋖ a) (hb : v ⋖ b) (hne : a ≠ b)
    (q : T → ℂ) : (Frame.complex a b ha hb hne).normalized q a = 0 := by
  simp [normalized, base]

omit [Fintype T] in
theorem complex_norm_one (a b : T) (ha : v ⋖ a) (hb : v ⋖ b) (hne : a ≠ b)
    (q : T → ℂ) (hq : 0 < (Frame.complex a b ha hb hne).radius q) :
    ‖(Frame.complex a b ha hb hne).normalized q b‖ = 1 := by
  dsimp [normalized, base, radius, pairRadius] at *
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    div_self hq.ne']

omit [Fintype T] in
theorem stableHeight_I (a : T) (ha : v ⋖ a) (q : T → ℂ)
    (hq : 0 < (Frame.stableHeight a ha).radius q) :
    (Frame.stableHeight a ha).normalized q a = Complex.I := by
  have hn : (q a).im ≠ 0 := hq.ne'
  apply Complex.ext <;> simp [normalized, base, radius, heightRadius, hn]

omit [Fintype T] in
/-- A positive real gap alone does not make either marked child center real. -/
theorem stableRealPair_zero (a b : T) (ha : v ⋖ a) (hb : v ⋖ b) (hne : a ≠ b)
    (q : T → ℂ) (hreal : (q a).im = 0) :
    (Frame.stableRealPair a b ha hb hne).normalized q a = 0 := by
  have heq : q a = ((q a).re : ℂ) := by
    apply Complex.ext <;> simp [hreal]
  change (q a - ((q a).re : ℂ)) / _ = 0
  rw [sub_eq_zero.mpr heq, zero_div]

omit [Fintype T] in
theorem stableRealPair_one (a b : T) (ha : v ⋖ a) (hb : v ⋖ b) (hne : a ≠ b)
    (q : T → ℂ) (hreal : (q b).im = 0)
    (hq : 0 < (Frame.stableRealPair a b ha hb hne).radius q) :
    (Frame.stableRealPair a b ha hb hne).normalized q b = 1 := by
  have heq : q b = ((q b).re : ℂ) := by
    apply Complex.ext <;> simp [hreal]
  dsimp [normalized, base, radius, orderedRealRadius] at *
  rw [heq, Complex.ofReal_re, ← Complex.ofReal_sub,
    div_self (Complex.ofReal_ne_zero.mpr hq.ne')]

end Frame

/-- Leaves have a fixed unused radius. Every internal radius is the actual gap
of its recursively constructed marked child centers. -/
def radius (F : Frames T) (p : T → ℂ) (v : T) : ℝ :=
  if hv : IsMax v then 1 else (F v hv).radius (centers T F p)

def PositiveGaps (F : Frames T) : Set (T → ℂ) :=
  {p | ∀ v, 0 < radius T F p v}

theorem radius_nonleaf (F : Frames T) (p : T → ℂ) (v : T) (hv : ¬ IsMax v) :
    radius T F p v = (F v hv).radius (centers T F p) := by
  simp [radius, hv]

theorem center_eq_frame_base (F : Frames T) (p : T → ℂ) (v : T) (hv : ¬ IsMax v) :
    center T F v p = (F v hv).base (centers T F p) := by
  rw [center_eq]
  cases hf : F v hv <;> simp [centerStep, hv, hf, Frame.base]

/-- Internal input positions are ignored by the recursion; only leaf values
determine the entire family of centers. -/
theorem center_congr_leaves (F : Frames T) (p q : T → ℂ)
    (hpq : ∀ v, IsMax v → p v = q v) (v : T) : center T F v p = center T F v q := by
  induction v using WellFoundedGT.induction with
  | ind v ih =>
    by_cases hv : IsMax v
    · rw [center_leaf T F v hv, center_leaf T F v hv, hpq v hv]
    · rw [center_eq_frame_base T F p v hv, center_eq_frame_base T F q v hv]
      cases hf : F v hv with
      | complex a b ha hb hne => exact ih a ha.lt
      | stableHeight a ha => exact congrArg (fun z : ℂ => (z.re : ℂ)) (ih a ha.lt)
      | stableRealPair a b ha hb hne =>
        exact congrArg (fun z : ℂ => (z.re : ℂ)) (ih a ha.lt)

theorem continuous_radius (F : Frames T) (v : T) : Continuous (fun p => radius T F p v) := by
  by_cases hv : IsMax v
  · simp only [radius, dif_pos hv]
    exact continuous_const
  · simp only [radius, dif_neg hv]
    exact (F v hv).continuous_radius.comp (centers T F).continuous

theorem isOpen_positiveGaps (F : Frames T) : IsOpen (PositiveGaps T F) := by
  change IsOpen {p | ∀ v, 0 < radius T F p v}
  simp only [Set.setOf_forall]
  apply isOpen_iInter_of_finite
  intro v
  exact isOpen_lt continuous_const (continuous_radius T F v)

theorem contDiffAt_radius (F : Frames T) (p : T → ℂ) (hp : p ∈ PositiveGaps T F) (v : T) :
    ContDiffAt ℝ ν (fun q => radius T F q v) p := by
  by_cases hv : IsMax v
  · simp only [radius, dif_pos hv]
    exact contDiffAt_const
  · simp only [radius, dif_neg hv]
    exact ((F v hv).contDiffAt_radius (centers T F p)
      (by simpa [radius, hv] using hp v)).comp p (contDiff_centers T F).contDiffAt

def normalized (F : Frames T) (p : T → ℂ) (v w : T) : ℂ :=
  (center T F w p - center T F v p) / (radius T F p v : ℂ)

theorem normalized_eq_frame (F : Frames T) (p : T → ℂ) (v : T) (hv : ¬ IsMax v) :
    normalized T F p v = (F v hv).normalized (centers T F p) := by
  funext w
  rw [normalized, center_eq_frame_base T F p v hv, radius_nonleaf T F p v hv]
  rfl

theorem contDiffAt_normalized (F : Frames T) (p : T → ℂ) (hp : p ∈ PositiveGaps T F)
    (v : T) : ContDiffAt ℝ ν (fun q => normalized T F q v) p := by
  apply contDiffAt_pi.mpr
  intro w
  simp only [normalized, div_eq_mul_inv]
  apply ContDiffAt.mul
  · exact (center T F w).contDiff.contDiffAt.sub (center T F v).contDiff.contDiffAt
  · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp p
      (contDiffAt_radius T F p hp v)).inv (Complex.ofReal_ne_zero.mpr (hp v).ne')

theorem normalized_complex_zero (F : Frames T) (p : T → ℂ) (v a b : T)
    (hv : ¬ IsMax v) (ha : v ⋖ a) (hb : v ⋖ b) (hne : a ≠ b)
    (hf : F v hv = .complex a b ha hb hne) : normalized T F p v a = 0 := by
  rw [normalized_eq_frame T F p v hv, hf]
  exact Frame.complex_zero a b ha hb hne _

theorem normalized_complex_norm_one (F : Frames T) (p : T → ℂ)
    (hp : p ∈ PositiveGaps T F) (v a b : T) (hv : ¬ IsMax v)
    (ha : v ⋖ a) (hb : v ⋖ b) (hne : a ≠ b)
    (hf : F v hv = .complex a b ha hb hne) : ‖normalized T F p v b‖ = 1 := by
  rw [normalized_eq_frame T F p v hv, hf]
  apply Frame.complex_norm_one
  simpa [radius, hv, hf] using hp v

theorem normalized_stableHeight_I (F : Frames T) (p : T → ℂ)
    (hp : p ∈ PositiveGaps T F) (v a : T) (hv : ¬ IsMax v) (ha : v ⋖ a)
    (hf : F v hv = .stableHeight a ha) : normalized T F p v a = Complex.I := by
  rw [normalized_eq_frame T F p v hv, hf]
  apply Frame.stableHeight_I
  simpa [radius, hv, hf] using hp v

theorem normalized_stableRealPair_zero (F : Frames T) (p : T → ℂ) (v a b : T)
    (hv : ¬ IsMax v) (ha : v ⋖ a) (hb : v ⋖ b) (hne : a ≠ b)
    (hf : F v hv = .stableRealPair a b ha hb hne) (hreal : (center T F a p).im = 0) :
    normalized T F p v a = 0 := by
  rw [normalized_eq_frame T F p v hv, hf]
  exact Frame.stableRealPair_zero a b ha hb hne _ hreal

theorem normalized_stableRealPair_one (F : Frames T) (p : T → ℂ)
    (hp : p ∈ PositiveGaps T F) (v a b : T) (hv : ¬ IsMax v)
    (ha : v ⋖ a) (hb : v ⋖ b) (hne : a ≠ b)
    (hf : F v hv = .stableRealPair a b ha hb hne) (hreal : (center T F b p).im = 0) :
    normalized T F p v b = 1 := by
  rw [normalized_eq_frame T F p v hv, hf]
  apply Frame.stableRealPair_one a b ha hb hne _ hreal
  simpa [radius, hv, hf] using hp v

open ForestNormalizationTelescope ForestInsertionDifference

/-- Actual adjacent-radius ratios, including root ratio one. The leaf ratios
are unused by insertion and can subsequently be fixed with `ForestLeafRadii`. -/
def localRadii (F : Frames T) (p : T → ℂ) : T → ℝ := localRadius T (radius T F p)

def increments (F : Frames T) (p : T → ℂ) : T → ℂ :=
  localIncrement T (radius T F p) (centers T F p)

theorem increments_child (F : Frames T) (p : T → ℂ) (v w : T) (hw : v ⋖ w) :
    increments T F p w = normalized T F p v w := by
  simp only [increments, localIncrement, hw.pred_eq, centers_apply, normalized,
    Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm]

theorem localRadii_pos (F : Frames T) (p : T → ℂ) (hp : p ∈ PositiveGaps T F) (v : T) :
    0 < localRadii T F p v := localRadius_pos T (radius T F p) hp v

theorem localRadii_root (F : Frames T) (p : T → ℂ) (hp : p ∈ PositiveGaps T F) :
    localRadii T F p ⊥ = 1 := localRadius_root T (radius T F p) hp

/-- Exact forward reconstruction, with centers and radii supplied by the
recursive frame factory itself. -/
theorem reconstruct (F : Frames T) (p : T → ℂ) (hp : p ∈ PositiveGaps T F) (v : T) :
    center T F ⊥ p + radius T F p ⊥ •
      position T (localRadii T F p) (increments T F p) v = center T F v p :=
  reconstruct_center T (radius T F p) hp (centers T F p) v

theorem reconstruct_leaf (F : Frames T) (p : T → ℂ) (hp : p ∈ PositiveGaps T F)
    (v : T) (hv : IsMax v) :
    center T F ⊥ p + radius T F p ⊥ •
      position T (localRadii T F p) (increments T F p) v = p v := by
  rw [reconstruct T F p hp v, center_leaf T F v hv]

theorem contDiffAt_localRadii (F : Frames T) (p : T → ℂ) (hp : p ∈ PositiveGaps T F) :
    ContDiffAt ℝ ν (localRadii T F) p := by
  apply contDiffAt_pi.mpr
  intro v
  exact (contDiffAt_radius T F p hp v).div (contDiffAt_radius T F p hp (Order.pred v))
    (hp (Order.pred v)).ne'

theorem contDiffAt_increments (F : Frames T) (p : T → ℂ) (hp : p ∈ PositiveGaps T F) :
    ContDiffAt ℝ ν (increments T F) p := by
  apply contDiffAt_pi.mpr
  intro v
  exact ((contDiffAt_radius T F p hp (Order.pred v)).inv (hp (Order.pred v)).ne').smul
    ((center T F v).contDiff.contDiffAt.sub (center T F (Order.pred v)).contDiff.contDiffAt)

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestMarkedFrames
