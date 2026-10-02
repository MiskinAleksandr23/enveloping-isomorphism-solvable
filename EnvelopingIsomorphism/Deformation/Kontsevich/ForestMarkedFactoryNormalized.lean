import EnvelopingIsomorphism.Deformation.Kontsevich.ForestMarkedFrameReflection
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestParameterSpace

/-! The actual marked factory satisfies its free normalized frame equations
on every reflected leaf input with positive marked gaps. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestMarkedFactoryNormalized

open ForestMarkedFrames ForestMarkedFrameInverse ForestMarkedFrameReflection
open ReflectedRadiusOrthant ComplexConjugate ForestInsertionDifference
open scoped Classical

variable (T : RootedTree) [Fintype T] (σ : T ≃o T) (F : Frames T)

def RealPairFixed : Prop := ∀ v hv a b ha hb hne,
  F v hv = Frame.stableRealPair a b ha hb hne → σ a = a ∧ σ b = b

variable (hF : ForestMarkedFrameReflection.Compatible T σ F)

include hF in
omit [Fintype T] in
theorem stableFixed : StableFixed T σ F := by
  intro v hv
  by_cases hs : σ v = v
  · cases F v hv <;> trivial
  · obtain ⟨a, b, ha, hb, hne, hf, _⟩ := hF.paired v hv hs
    simp only [hf]

include hF in
theorem center_fixed_im (p : T → ℂ) (hp : ∀ v, IsMax v → p (σ v) = conj (p v))
    (v : T) (hv : σ v = v) : (center T F v p).im = 0 := by
  have h := center_reflection T σ F hF p hp v
  rw [hv] at h
  exact Complex.conj_eq_iff_im.mp h.symm

variable (hpair : RealPairFixed T σ F)

include hF hpair in
theorem normalized_factory (p : T → ℂ) (hp : ∀ v, IsMax v → p (σ v) = conj (p v))
    (hpos : p ∈ PositiveGaps T F) : Normalized T F (localRadii T F p) (increments T F p) := by
  intro v hv
  have hfFix := stableFixed T σ F hF v hv
  have hstable : σ v = v → (position T (localRadii T F p) (increments T F p) v).im = 0 := by
    intro hs
    exact ReflectedForestInsertion.position_im_eq_zero_of_fixed T σ _
      (localRadii_reflection T σ F hF p hp) _ (increments_reflection T σ F hF p hp) v hs
  cases hf : F v hv with
  | complex a b ha hb hne =>
    constructor
    · rw [increments_child T F p v a ha]
      exact normalized_complex_zero T F p v a b hv ha hb hne hf
    · rw [increments_child T F p v b hb]
      exact normalized_complex_norm_one T F p hpos v a b hv ha hb hne hf
  | stableHeight a ha =>
    rw [hf] at hfFix
    constructor
    · rw [increments_child T F p v a ha]
      exact normalized_stableHeight_I T F p hpos v a hv ha hf
    · exact hstable hfFix
  | stableRealPair a b ha hb hne =>
    rw [hf] at hfFix
    have hmarks := hpair v hv a b ha hb hne hf
    refine ⟨?_, ?_, hstable hfFix⟩
    · rw [increments_child T F p v a ha]
      exact normalized_stableRealPair_zero T F p v a b hv ha hb hne hf
        (center_fixed_im T σ F hF p hp a hmarks.1)
    · rw [increments_child T F p v b hb]
      exact normalized_stableRealPair_one T F p hpos v a b hv ha hb hne hf
        (center_fixed_im T σ F hF p hp b hmarks.2)

include hF hpair in
theorem constraints_factory (p : T → ℂ) (hp : ∀ v, IsMax v → p (σ v) = conj (p v))
    (hpos : p ∈ PositiveGaps T F) :
    ForestParameterSpace.Constraints T σ F (ForestLeafRadii.fixLeaves T (localRadii T F p), increments T F p) := by
  have hrad := fixedLocalRadii_reflection T σ F hF p hp
  have hinc := increments_reflection T σ F hF p hp
  refine ⟨⟨?_, ?_, hrad, ?_⟩, ?_, hinc, ?_⟩
  · by_cases hroot : IsMax (⊥ : T)
    · simp [ForestLeafRadii.fixLeaves, hroot]
    · simp only [ForestLeafRadii.fixLeaves, if_neg hroot]
      exact localRadii_root T F p hpos
  · intro v hv
    simp [ForestLeafRadii.fixLeaves, hv]
  · intro v
    by_cases hv : IsMax v
    · simp [ForestLeafRadii.fixLeaves, hv]
    · simpa only [ForestLeafRadii.fixLeaves, if_neg hv] using (localRadii_pos T F p hpos v).le
  · exact normalized_change_radii T σ F (stableFixed T σ F hF) _ _ hrad _ hinc
      (normalized_factory T σ F hF hpair p hp hpos)
  · simp [increments, ForestNormalizationTelescope.localIncrement]

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestMarkedFactoryNormalized
