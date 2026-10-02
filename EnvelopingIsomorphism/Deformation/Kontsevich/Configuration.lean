import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# Ordered half-plane configurations and affine normalization

Configurations have distinct labelled interior points and increasingly ordered
boundary points. Positive real affine transformations act on both sets of
points. Choosing any interior label gives the normalization sending that point
to `I`; the normalized configurations explicitly parametrize affine orbits.

This file concerns the open configuration spaces only. It makes no claim about
compactifications, integration of angle forms, or graph-weight identities.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open scoped UpperHalfPlane

/-- A real affine transformation `z ↦ scale * z + shift` with positive scale. -/
structure PositiveAffine where
  scale : ℝ
  shift : ℝ
  scale_pos : 0 < scale

namespace PositiveAffine

@[ext] theorem ext {g h : PositiveAffine} (ha : g.scale = h.scale)
    (hb : g.shift = h.shift) : g = h := by
  cases g
  cases h
  cases ha
  cases hb
  rfl

def identity : PositiveAffine := ⟨1, 0, zero_lt_one⟩

/-- Composition, with the right factor applied first. -/
def comp (g h : PositiveAffine) : PositiveAffine :=
  ⟨g.scale * h.scale, g.scale * h.shift + g.shift, mul_pos g.scale_pos h.scale_pos⟩

def inverse (g : PositiveAffine) : PositiveAffine :=
  ⟨g.scale⁻¹, -g.shift / g.scale, inv_pos.mpr g.scale_pos⟩

def onReal (g : PositiveAffine) (x : ℝ) : ℝ := g.scale * x + g.shift

def onUpper (g : PositiveAffine) (z : ℍ) : ℍ :=
  ⟨⟨g.scale * z.re + g.shift, g.scale * z.im⟩, mul_pos g.scale_pos z.im_pos⟩

@[simp] theorem onUpper_re (g : PositiveAffine) (z : ℍ) :
    (g.onUpper z).re = g.scale * z.re + g.shift := rfl

@[simp] theorem onUpper_im (g : PositiveAffine) (z : ℍ) :
    (g.onUpper z).im = g.scale * z.im := rfl

/-- The coordinate action is the usual complex affine transformation. -/
theorem coe_onUpper (g : PositiveAffine) (z : ℍ) :
    (g.onUpper z : ℂ) = (g.scale : ℂ) * (z : ℂ) + (g.shift : ℂ) := by
  apply Complex.ext <;> simp

theorem onReal_strictMono (g : PositiveAffine) : StrictMono g.onReal := by
  intro x y h
  dsimp [onReal]
  linarith [mul_lt_mul_of_pos_left h g.scale_pos]

theorem onUpper_injective (g : PositiveAffine) : Function.Injective g.onUpper := by
  intro z w h
  apply UpperHalfPlane.ext_re_im
  · have hr := congrArg UpperHalfPlane.re h
    simp only [onUpper_re, add_left_inj] at hr
    exact mul_left_cancel₀ (ne_of_gt g.scale_pos) hr
  · have hi := congrArg UpperHalfPlane.im h
    simp only [onUpper_im] at hi
    exact mul_left_cancel₀ (ne_of_gt g.scale_pos) hi

@[simp] theorem onReal_identity (x : ℝ) : identity.onReal x = x := by
  simp [onReal, identity]

@[simp] theorem onUpper_identity (z : ℍ) : identity.onUpper z = z := by
  apply UpperHalfPlane.ext_re_im <;> simp [identity]

theorem onReal_comp (g h : PositiveAffine) (x : ℝ) :
    (g.comp h).onReal x = g.onReal (h.onReal x) := by
  simp only [onReal, comp]
  ring

theorem onUpper_comp (g h : PositiveAffine) (z : ℍ) :
    (g.comp h).onUpper z = g.onUpper (h.onUpper z) := by
  apply UpperHalfPlane.ext_re_im <;> simp only [onUpper_re, onUpper_im, comp] <;> ring

@[simp] theorem inverse_comp (g : PositiveAffine) : g.inverse.comp g = identity := by
  have ha := ne_of_gt g.scale_pos
  ext <;> dsimp [inverse, comp, identity] <;> field_simp [ha]
  all_goals ring

@[simp] theorem comp_inverse (g : PositiveAffine) : g.comp g.inverse = identity := by
  have ha := ne_of_gt g.scale_pos
  ext <;> dsimp [inverse, comp, identity] <;> field_simp [ha]
  all_goals ring

end PositiveAffine

/-- The component of labelled configurations with increasing boundary labels. -/
structure Configuration (n m : ℕ) where
  interior : Fin n → ℍ
  boundary : Fin m → ℝ
  interior_injective : Function.Injective interior
  boundary_strictMono : StrictMono boundary

namespace Configuration

variable {n m : ℕ}

@[ext] theorem ext {c d : Configuration n m} (hp : c.interior = d.interior)
    (hq : c.boundary = d.boundary) : c = d := by
  cases c
  cases d
  cases hp
  cases hq
  rfl

/-- The complex coordinate attached to a graph vertex of either type. -/
def vertexPoint (c : Configuration n m) : Fin n ⊕ Fin m → ℂ :=
  Sum.elim (fun i => (c.interior i : ℂ)) (fun j => (c.boundary j : ℂ))

/-- Interior and boundary labels together give distinct complex points. -/
theorem vertexPoint_injective (c : Configuration n m) : Function.Injective c.vertexPoint := by
  intro u v h
  cases u with
  | inl i =>
    cases v with
    | inl j =>
      exact congrArg Sum.inl (c.interior_injective (UpperHalfPlane.ext h))
    | inr j =>
      have hz : (c.interior i).im = 0 := by
        simpa [vertexPoint] using congrArg Complex.im h
      exact False.elim ((c.interior i).im_ne_zero hz)
  | inr i =>
    cases v with
    | inl j =>
      have hz : (c.interior j).im = 0 := by
        simpa [vertexPoint] using (congrArg Complex.im h).symm
      exact False.elim ((c.interior j).im_ne_zero hz)
    | inr j =>
      exact congrArg Sum.inr (c.boundary_strictMono.injective (Complex.ofReal_injective h))

theorem vertexPoint_sub_ne_zero (c : Configuration n m) {u v : Fin n ⊕ Fin m}
    (h : u ≠ v) : c.vertexPoint u - c.vertexPoint v ≠ 0 :=
  sub_ne_zero.mpr (fun heq => h (c.vertexPoint_injective heq))

/-- The diagonal positive affine action. -/
def act (g : PositiveAffine) (c : Configuration n m) : Configuration n m where
  interior := g.onUpper ∘ c.interior
  boundary := g.onReal ∘ c.boundary
  interior_injective := g.onUpper_injective.comp c.interior_injective
  boundary_strictMono := g.onReal_strictMono.comp c.boundary_strictMono

@[simp] theorem act_interior (g : PositiveAffine) (c : Configuration n m) (i : Fin n) :
    (act g c).interior i = g.onUpper (c.interior i) := rfl

@[simp] theorem act_boundary (g : PositiveAffine) (c : Configuration n m) (j : Fin m) :
    (act g c).boundary j = g.onReal (c.boundary j) := rfl

@[simp] theorem act_identity (c : Configuration n m) : act .identity c = c := by
  ext i <;> simp

theorem act_comp (g h : PositiveAffine) (c : Configuration n m) :
    act (g.comp h) c = act g (act h c) := by
  apply ext
  · funext i
    exact PositiveAffine.onUpper_comp g h _
  · funext i
    exact PositiveAffine.onReal_comp g h _

@[simp] theorem act_inverse_act (g : PositiveAffine) (c : Configuration n m) :
    act g.inverse (act g c) = c := by
  rw [← act_comp, PositiveAffine.inverse_comp, act_identity]

@[simp] theorem act_act_inverse (g : PositiveAffine) (c : Configuration n m) :
    act g (act g.inverse c) = c := by
  rw [← act_comp, PositiveAffine.comp_inverse, act_identity]

/-- With an interior point present, the affine action has no nonidentity stabilizers. -/
theorem act_eq_self_iff (i : Fin n) (g : PositiveAffine) (c : Configuration n m) :
    act g c = c ↔ g = .identity := by
  constructor
  · intro h
    have hp := congrArg (fun d : Configuration n m => d.interior i) h
    have hr := congrArg UpperHalfPlane.re hp
    have hi := congrArg UpperHalfPlane.im hp
    simp only [act_interior, PositiveAffine.onUpper_re] at hr
    simp only [act_interior, PositiveAffine.onUpper_im] at hi
    have ha : g.scale = 1 := by nlinarith [(c.interior i).im_pos]
    apply PositiveAffine.ext ha
    change g.shift = 0
    simpa [ha] using hr
  · rintro rfl
    exact act_identity c

/-- The unique candidate affine transformation sending the chosen point to `I`. -/
def normalizer (i : Fin n) (c : Configuration n m) : PositiveAffine :=
  ⟨(c.interior i).im⁻¹, -(c.interior i).re / (c.interior i).im,
    inv_pos.mpr (c.interior i).im_pos⟩

def normalize (i : Fin n) (c : Configuration n m) : Configuration n m :=
  act (normalizer i c) c

@[simp] theorem normalize_interior (i : Fin n) (c : Configuration n m) :
    (normalize i c).interior i = UpperHalfPlane.I := by
  apply UpperHalfPlane.ext_re_im
  · simp [normalize, normalizer, div_eq_mul_inv, mul_comm]
  · simp [normalize, normalizer, (c.interior i).im_ne_zero]

theorem normalize_act (i : Fin n) (g : PositiveAffine) (c : Configuration n m) :
    normalize i (act g c) = normalize i c := by
  have ha := ne_of_gt g.scale_pos
  have hz := (c.interior i).im_ne_zero
  apply ext
  · funext j
    apply UpperHalfPlane.ext_re_im <;>
      simp only [normalize, act_interior, PositiveAffine.onUpper_re,
        PositiveAffine.onUpper_im, normalizer] <;> field_simp [ha, hz]
    all_goals ring
  · funext j
    simp only [normalize, act_boundary, PositiveAffine.onReal, normalizer,
      act_interior, PositiveAffine.onUpper_re, PositiveAffine.onUpper_im]
    field_simp [ha, hz]
    ring

theorem normalize_eq_self (i : Fin n) (c : Configuration n m)
    (hc : c.interior i = UpperHalfPlane.I) : normalize i c = c := by
  have h : normalizer i c = .identity := by
    ext <;> simp [normalizer, PositiveAffine.identity, hc]
  rw [normalize, h, act_identity]

/-- Configurations with the distinguished interior point fixed at `I`. -/
def Normalized (i : Fin n) (m : ℕ) :=
  {c : Configuration n m // c.interior i = UpperHalfPlane.I}

def normalized (i : Fin n) (c : Configuration n m) : Normalized i m :=
  ⟨normalize i c, normalize_interior i c⟩

/-- Two configurations differ by an orientation-preserving real affine map. -/
def AffineRelated (c d : Configuration n m) : Prop := ∃ g, act g c = d

theorem affineRelated_iff_normalize_eq (i : Fin n) (c d : Configuration n m) :
    AffineRelated c d ↔ normalize i c = normalize i d := by
  constructor
  · rintro ⟨g, rfl⟩
    exact (normalize_act i g c).symm
  · intro h
    refine ⟨(normalizer i d).inverse.comp (normalizer i c), ?_⟩
    rw [act_comp]
    change act (normalizer i d).inverse (normalize i c) = d
    rw [h]
    exact act_inverse_act _ _

/-- The genuine orbit equivalence relation, defined independently of normalization. -/
def affineSetoid (n m : ℕ) : Setoid (Configuration n m) where
  r := AffineRelated
  iseqv := {
    refl := fun c => ⟨.identity, act_identity c⟩
    symm := by
      rintro c d ⟨g, rfl⟩
      exact ⟨g.inverse, act_inverse_act g c⟩
    trans := by
      rintro c d e ⟨g, rfl⟩ ⟨h, rfl⟩
      exact ⟨h.comp g, act_comp h g c⟩ }

def AffineQuotient (n m : ℕ) := Quotient (affineSetoid n m)

/-- Every affine orbit has exactly one normalized representative. -/
def quotientEquivNormalized (i : Fin n) : AffineQuotient n m ≃ Normalized i m where
  toFun := Quotient.lift (normalized i) (by
    intro c d h
    exact Subtype.ext ((affineRelated_iff_normalize_eq i c d).mp h))
  invFun c := Quotient.mk (affineSetoid n m) c.val
  left_inv := by
    intro q
    refine Quotient.inductionOn q fun c => ?_
    apply Quotient.sound
    exact ⟨(normalizer i c).inverse, act_inverse_act _ _⟩
  right_inv := by
    intro c
    exact Subtype.ext (normalize_eq_self i c.val c.property)

end Configuration

end EnvelopingIsomorphism.Deformation.Kontsevich
