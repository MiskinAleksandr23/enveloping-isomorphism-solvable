import EnvelopingIsomorphism.Deformation.Kontsevich.ForestParameterSpace

/-! Reflection separates the normalized shape equations from the radial
parameters. Stable cumulative-position reality is derived, not an additional
radial constraint in the product model. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestParameterProduct

open ForestMarkedFrames ForestMarkedFrameInverse ForestParameterSpace ComplexConjugate
open scoped Topology Classical

variable (T : RootedTree) [Fintype T] (σ : T ≃o T) (F : Frames T)

def ShapeNormalized (a : T → ℂ) : Prop :=
  ∀ v (hv : ¬ IsMax v), match F v hv with
    | .complex b c _ _ _ => a b = 0 ∧ ‖a c‖ = 1
    | .stableHeight b _ => a b = Complex.I
    | .stableRealPair b c _ _ _ => a b = 0 ∧ a c = 1

def ShapeConstraints (a : T → ℂ) : Prop :=
  ShapeNormalized T F a ∧ (∀ u, a (σ u) = conj (a u)) ∧ a ⊥ = 0

theorem normalized_iff_shape (hF : ReflectedRadiusOrthant.StableFixed T σ F)
    (r : T → ℝ) (a : T → ℂ) (hr : ∀ u, r (σ u) = r u)
    (ha : ∀ u, a (σ u) = conj (a u)) : Normalized T F r a ↔ ShapeNormalized T F a := by
  constructor
  · intro hn v hv
    have h := hn v hv
    cases hf : F v hv with
    | complex b c hb hc hbc => simpa only [hf] using h
    | stableHeight b hb =>
      rw [hf] at h
      exact h.1
    | stableRealPair b c hb hc hbc =>
      rw [hf] at h
      exact ⟨h.1, h.2.1⟩
  · intro hn v hv
    have h := hn v hv
    have hfixed := hF v hv
    cases hf : F v hv with
    | complex b c hb hc hbc => simpa only [hf] using h
    | stableHeight b hb =>
      rw [hf] at h hfixed
      exact ⟨h, ReflectedForestInsertion.position_im_eq_zero_of_fixed T σ r hr a ha v hfixed⟩
    | stableRealPair b c hb hc hbc =>
      rw [hf] at h hfixed
      exact ⟨h.1, h.2,
        ReflectedForestInsertion.position_im_eq_zero_of_fixed T σ r hr a ha v hfixed⟩

theorem constraints_iff_product (hF : ReflectedRadiusOrthant.StableFixed T σ F)
    (x : Ambient T) : Constraints T σ F x ↔
      ReflectedRadiusOrthant.Admissible T σ x.1 ∧ ShapeConstraints T σ F x.2 := by
  constructor
  · rintro ⟨hr, hn, ha, hzero⟩
    exact ⟨hr, (normalized_iff_shape T σ F hF _ _ hr.2.2.1 ha).mp hn, ha, hzero⟩
  · rintro ⟨hr, hn, ha, hzero⟩
    exact ⟨hr, (normalized_iff_shape T σ F hF _ _ hr.2.2.1 ha).mpr hn, ha, hzero⟩

abbrev RadiusSpace := {r : T → ℝ // ReflectedRadiusOrthant.Admissible T σ r}
abbrev ShapeSpace := {a : T → ℂ // ShapeConstraints T σ F a}

/-- The actual normalized reflected parameter space is a product of its
radial orthant and its shape space. The underlying map is coordinate projection. -/
def productHomeomorph (hF : ReflectedRadiusOrthant.StableFixed T σ F) :
    Space T σ F ≃ₜ RadiusSpace T σ × ShapeSpace T σ F where
  toEquiv :=
    { toFun := fun x =>
        (⟨x.val.1, ((constraints_iff_product T σ F hF x.val).mp x.property).1⟩,
          ⟨x.val.2, ((constraints_iff_product T σ F hF x.val).mp x.property).2⟩)
      invFun := fun x => ⟨(x.1.val, x.2.val),
        (constraints_iff_product T σ F hF _).mpr ⟨x.1.property, x.2.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestParameterProduct
