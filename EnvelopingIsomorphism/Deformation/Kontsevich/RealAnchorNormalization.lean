import EnvelopingIsomorphism.Deformation.Kontsevich.DirectionRatioInvariant

/-!
# Normalization at two ordered real boundary anchors

The actual positive affine map sends the chosen ordered boundary points to
zero and one. No interior label is required. The resulting native normalized
configuration space parametrizes the existing affine orbit quotient and has
an explicit transition to every available interior-anchor normalization.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.Configuration

open Topology Set ComplexConjugate

variable {n m : ℕ}

def realGap (a b : Fin m) (c : Configuration n m) : ℝ := c.boundary b - c.boundary a

theorem realGap_pos (a b : Fin m) (hab : a < b) (c : Configuration n m) :
    0 < realGap a b c := sub_pos.mpr (c.boundary_strictMono hab)

/-- The unique positive affine candidate sending the two chosen points to zero and one. -/
def realNormalizer (a b : Fin m) (hab : a < b) (c : Configuration n m) : PositiveAffine :=
  ⟨(realGap a b c)⁻¹, -c.boundary a / realGap a b c, inv_pos.mpr (realGap_pos a b hab c)⟩

def realNormalize (a b : Fin m) (hab : a < b) (c : Configuration n m) : Configuration n m :=
  act (realNormalizer a b hab c) c

@[simp] theorem realNormalize_boundary_left (a b : Fin m) (hab : a < b) (c : Configuration n m) :
    (realNormalize a b hab c).boundary a = 0 := by
  simp only [realNormalize, act_boundary, PositiveAffine.onReal, realNormalizer, div_eq_mul_inv]
  ring

@[simp] theorem realNormalize_boundary_right (a b : Fin m) (hab : a < b) (c : Configuration n m) :
    (realNormalize a b hab c).boundary b = 1 := by
  change (realGap a b c)⁻¹ * c.boundary b + -c.boundary a / realGap a b c = 1
  calc
    _ = (realGap a b c)⁻¹ * realGap a b c := by simp only [realGap, div_eq_mul_inv]; ring
    _ = 1 := inv_mul_cancel₀ (realGap_pos a b hab c).ne'

/-- This uniqueness proof uses only the two ordered real anchors, even if there are no interiors. -/
theorem realNormalizer_unique (a b : Fin m) (hab : a < b) (c : Configuration n m)
    (g : PositiveAffine) (hzero : (act g c).boundary a = 0) (hone : (act g c).boundary b = 1) :
    g = realNormalizer a b hab c := by
  change g.scale * c.boundary a + g.shift = 0 at hzero
  change g.scale * c.boundary b + g.shift = 1 at hone
  have hs : g.scale * realGap a b c = 1 := by
    dsimp [realGap]
    nlinarith
  have hscale : g.scale = (realGap a b c)⁻¹ := by
    apply mul_right_cancel₀ (realGap_pos a b hab c).ne'
    rw [hs, inv_mul_cancel₀ (realGap_pos a b hab c).ne']
  apply PositiveAffine.ext hscale
  change g.shift = -c.boundary a / realGap a b c
  have hshift : g.shift = -(g.scale * c.boundary a) := by linarith
  rw [hshift, hscale]
  simp only [div_eq_mul_inv]
  ring

theorem realNormalizer_act_comp (a b : Fin m) (hab : a < b)
    (g : PositiveAffine) (c : Configuration n m) :
    (realNormalizer a b hab (act g c)).comp g = realNormalizer a b hab c := by
  apply realNormalizer_unique a b hab c
  · rw [act_comp]
    exact realNormalize_boundary_left a b hab (act g c)
  · rw [act_comp]
    exact realNormalize_boundary_right a b hab (act g c)

theorem realNormalize_act (a b : Fin m) (hab : a < b)
    (g : PositiveAffine) (c : Configuration n m) :
    realNormalize a b hab (act g c) = realNormalize a b hab c := by
  rw [realNormalize, ← act_comp, realNormalizer_act_comp]
  rfl

theorem realNormalize_eq_self (a b : Fin m) (hab : a < b) (c : Configuration n m)
    (ha : c.boundary a = 0) (hb : c.boundary b = 1) : realNormalize a b hab c = c := by
  have h : realNormalizer a b hab c = PositiveAffine.identity := by
    apply PositiveAffine.ext <;> simp [realNormalizer, realGap, ha, hb, PositiveAffine.identity]
  rw [realNormalize, h, act_identity]

/-- Native configurations whose chosen real anchors are zero and one. -/
def RealNormalized (a b : Fin m) (n : ℕ) :=
  {c : Configuration n m // c.boundary a = 0 ∧ c.boundary b = 1}

instance (a b : Fin m) : TopologicalSpace (RealNormalized a b n) :=
  inferInstanceAs (TopologicalSpace {c : Configuration n m // c.boundary a = 0 ∧ c.boundary b = 1})

def realNormalized (a b : Fin m) (hab : a < b) (c : Configuration n m) : RealNormalized a b n :=
  ⟨realNormalize a b hab c, realNormalize_boundary_left a b hab c, realNormalize_boundary_right a b hab c⟩

@[simp] theorem realNormalized_val (a b : Fin m) (hab : a < b) (c : Configuration n m) :
    (realNormalized a b hab c).val = realNormalize a b hab c := rfl

theorem affineRelated_iff_realNormalize_eq (a b : Fin m) (hab : a < b) (c e : Configuration n m) :
    AffineRelated c e ↔ realNormalize a b hab c = realNormalize a b hab e := by
  constructor
  · rintro ⟨g, rfl⟩
    exact (realNormalize_act a b hab g c).symm
  · intro h
    refine ⟨(realNormalizer a b hab e).inverse.comp (realNormalizer a b hab c), ?_⟩
    rw [act_comp]
    change act (realNormalizer a b hab e).inverse (realNormalize a b hab c) = e
    rw [h]
    exact act_inverse_act _ _

/-- Every actual affine orbit has a unique representative in the real-anchor frame. -/
def quotientEquivRealNormalized (a b : Fin m) (hab : a < b) :
    AffineQuotient n m ≃ RealNormalized a b n where
  toFun := Quotient.lift (realNormalized a b hab) (by
    intro c e h
    exact Subtype.ext ((affineRelated_iff_realNormalize_eq a b hab c e).mp h))
  invFun c := Quotient.mk (affineSetoid n m) c.val
  left_inv q := by
    refine Quotient.inductionOn q fun c ↦ ?_
    apply Quotient.sound
    exact ⟨(realNormalizer a b hab c).inverse, act_inverse_act _ _⟩
  right_inv c := Subtype.ext (realNormalize_eq_self a b hab c.val c.property.1 c.property.2)

/-- The native transition sends each representative to the other normalization
of the same labelled configuration, without a label permutation. -/
def interiorRealEquiv (i : Fin n) (a b : Fin m) (hab : a < b) :
    Normalized i m ≃ RealNormalized a b n where
  toFun c := realNormalized a b hab c.val
  invFun c := normalized i c.val
  left_inv c := by
    apply Subtype.ext
    change normalize i (realNormalize a b hab c.val) = c.val
    rw [realNormalize, normalize_act, normalize_eq_self i c.val c.property]
  right_inv c := by
    apply Subtype.ext
    change realNormalize a b hab (normalize i c.val) = c.val
    rw [normalize, realNormalize_act, realNormalize_eq_self a b hab c.val c.property.1 c.property.2]

/-- All vertex coordinates have the same positive-denominator normalization formula. -/
theorem realNormalize_vertexPoint (a b : Fin m) (hab : a < b) (c : Configuration n m)
    (v : Fin n ⊕ Fin m) :
    (realNormalize a b hab c).vertexPoint v =
      (c.vertexPoint v - (c.boundary a : ℂ)) / (realGap a b c : ℂ) := by
  rw [realNormalize, act_vertexPoint]
  simp only [realNormalizer, div_eq_mul_inv]
  push_cast
  ring

theorem realNormalize_boundary (a b : Fin m) (hab : a < b) (c : Configuration n m) (j : Fin m) :
    (realNormalize a b hab c).boundary j = (c.boundary j - c.boundary a) / realGap a b c := by
  simp only [realNormalize, act_boundary, PositiveAffine.onReal, realNormalizer, div_eq_mul_inv]
  ring

@[fun_prop] theorem continuous_boundaryCoordinate (j : Fin m) :
    Continuous (fun c : Configuration n m ↦ c.boundary j) := by
  simpa only [Function.comp_def, vertexPoint, Sum.elim_inr, Complex.ofReal_re] using
    Complex.continuous_re.comp (continuous_vertexCoordinate (n := n) (Sum.inr j))

@[fun_prop] theorem continuous_realGap (a b : Fin m) :
    Continuous (realGap a b : Configuration n m → ℝ) :=
  (continuous_boundaryCoordinate b).sub (continuous_boundaryCoordinate a)

@[fun_prop] theorem continuous_realNormalize (a b : Fin m) (hab : a < b) :
    Continuous (realNormalize a b hab : Configuration n m → Configuration n m) := by
  apply isEmbedding_vertexCoordinates.continuous_iff.mpr
  apply continuous_pi
  intro v
  change Continuous (fun c : Configuration n m ↦ (realNormalize a b hab c).vertexPoint v)
  simp only [realNormalize_vertexPoint]
  exact ((continuous_vertexCoordinate v).sub
    (Complex.continuous_ofReal.comp (continuous_boundaryCoordinate a))).div
      (Complex.continuous_ofReal.comp (continuous_realGap a b))
      (fun c ↦ Complex.ofReal_ne_zero.mpr (realGap_pos a b hab c).ne')

@[fun_prop] theorem continuous_realNormalized (a b : Fin m) (hab : a < b) :
    Continuous (realNormalized a b hab : Configuration n m → RealNormalized a b n) :=
  (continuous_realNormalize a b hab).subtype_mk _

/-- The interior-normalization formula on every original vertex, for the native transition. -/
theorem normalize_vertexPoint (i : Fin n) (c : Configuration n m) (v : Fin n ⊕ Fin m) :
    (normalize i c).vertexPoint v =
      (c.vertexPoint v - ((c.interior i).re : ℂ)) / ((c.interior i).im : ℂ) := by
  rw [normalize, act_vertexPoint]
  simp only [normalizer, div_eq_mul_inv]
  push_cast
  ring

@[fun_prop] theorem continuous_normalize (i : Fin n) :
    Continuous (normalize i : Configuration n m → Configuration n m) := by
  apply isEmbedding_vertexCoordinates.continuous_iff.mpr
  apply continuous_pi
  intro v
  change Continuous (fun c : Configuration n m ↦ (normalize i c).vertexPoint v)
  simp only [normalize_vertexPoint]
  have hre : Continuous (fun c : Configuration n m ↦ ((c.interior i).re : ℂ)) :=
    Complex.continuous_ofReal.comp (Complex.continuous_re.comp (continuous_vertexCoordinate (Sum.inl i)))
  have him : Continuous (fun c : Configuration n m ↦ ((c.interior i).im : ℂ)) :=
    Complex.continuous_ofReal.comp (Complex.continuous_im.comp (continuous_vertexCoordinate (Sum.inl i)))
  exact ((continuous_vertexCoordinate v).sub hre).div him
    (fun c ↦ Complex.ofReal_ne_zero.mpr (c.interior i).im_ne_zero)

@[fun_prop] theorem continuous_normalized (i : Fin n) :
    Continuous (normalized i : Configuration n m → Normalized i m) :=
  (continuous_normalize i).subtype_mk _

/-- The two native normalized configuration spaces have the actual continuous inverse transitions. -/
def interiorRealHomeomorph (i : Fin n) (a b : Fin m) (hab : a < b) :
    Normalized i m ≃ₜ RealNormalized a b n where
  __ := interiorRealEquiv i a b hab
  continuous_toFun := (continuous_realNormalized a b hab).comp continuous_subtype_val
  continuous_invFun := (continuous_normalized i).comp continuous_subtype_val

@[simp] theorem interiorRealHomeomorph_apply (i : Fin n) (a b : Fin m) (hab : a < b)
    (c : Normalized i m) : interiorRealHomeomorph i a b hab c = realNormalized a b hab c.val := rfl

@[simp] theorem interiorRealHomeomorph_symm_apply (i : Fin n) (a b : Fin m) (hab : a < b)
    (c : RealNormalized a b n) : (interiorRealHomeomorph i a b hab).symm c = normalized i c.val := rfl

/-- A canonical real-only configuration shows the frame does not require an interior point. -/
def realOnlyConfiguration (m : ℕ) : Configuration 0 m where
  interior := Fin.elim0
  boundary j := j.val
  interior_injective := by intro j; exact Fin.elim0 j
  boundary_strictMono := by
    intro j k hjk
    change (j.val : ℝ) < (k.val : ℝ)
    exact Nat.cast_lt.mpr hjk

def realOnlyNormalized (a b : Fin m) (hab : a < b) : RealNormalized a b 0 :=
  realNormalized a b hab (realOnlyConfiguration m)

theorem nonempty_realOnlyNormalized (a b : Fin m) (hab : a < b) : Nonempty (RealNormalized a b 0) :=
  ⟨realOnlyNormalized a b hab⟩

/-- Full doubled directions and all triple ratios are preserved by the real normalization. -/
@[simp] theorem directionRatioCoordinates_realNormalize (a b : Fin m) (hab : a < b)
    (c : Configuration n m) :
    directionRatioCoordinates (realNormalize a b hab c) = directionRatioCoordinates c :=
  directionRatioCoordinates_act (realNormalizer a b hab c) c

def realDirectionRatios {a b : Fin m} (c : RealNormalized a b n) : DRData n m :=
  directionRatioCoordinates c.val

@[fun_prop] theorem continuous_realDirectionRatios (a b : Fin m) :
    Continuous (realDirectionRatios : RealNormalized a b n → DRData n m) :=
  continuous_directionRatioCoordinates.comp continuous_subtype_val

@[simp] theorem interiorRealHomeomorph_directionRatios (i : Fin n) (a b : Fin m) (hab : a < b)
    (c : Normalized i m) :
    realDirectionRatios (interiorRealHomeomorph i a b hab c) = normalizedDirectionRatios c :=
  directionRatioCoordinates_realNormalize a b hab c.val

theorem range_realDirectionRatios_eq_configuration (a b : Fin m) (hab : a < b) :
    Set.range (realDirectionRatios : RealNormalized a b n → DRData n m) =
      Set.range (directionRatioCoordinates : Configuration n m → DRData n m) := by
  ext z
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c.val, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨realNormalized a b hab c, directionRatioCoordinates_realNormalize a b hab c⟩

theorem directionRatioSet_eq_realNormalized (a b : Fin m) (hab : a < b) :
    directionRatioSet n m = closure (Set.range (realDirectionRatios : RealNormalized a b n → DRData n m)) := by
  rw [range_realDirectionRatios_eq_configuration a b hab]
  rfl

theorem range_realDirectionRatios_eq_interior (i : Fin n) (a b : Fin m) (hab : a < b) :
    Set.range (realDirectionRatios : RealNormalized a b n → DRData n m) =
      Set.range (normalizedDirectionRatios : Normalized i m → DRData n m) := by
  rw [range_realDirectionRatios_eq_configuration a b hab,
    range_normalizedDirectionRatios_eq_configuration i]

end EnvelopingIsomorphism.Deformation.Kontsevich.Configuration
