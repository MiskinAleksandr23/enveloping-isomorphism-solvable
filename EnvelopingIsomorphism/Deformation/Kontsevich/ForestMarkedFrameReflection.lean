import EnvelopingIsomorphism.Deformation.Kontsevich.ForestMarkedFrames
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestLeafRadii

/-! Reflection of actual recursively marked centers and parameters. Only the
input leaf positions must intertwine reflection with complex conjugation. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestMarkedFrameReflection

open ForestMarkedFrames ComplexConjugate
open scoped Classical

variable (T : RootedTree) [Fintype T] (σ : T ≃o T)

omit [Fintype T] in
theorem nonleaf_reflect (v : T) (hv : ¬IsMax v) : ¬IsMax (σ v) :=
  fun h => hv (σ.isMax_apply.mp h)

/-- Stable nodes use real-centered frame kinds. Nonstable nodes use ordered
complex marks transported exactly to their paired node. -/
structure Compatible (F : Frames T) : Prop where
  stable : ∀ v hv, σ v = v →
    (∃ a ha, F v hv = .stableHeight a ha) ∨
      ∃ a b ha hb hne, F v hv = .stableRealPair a b ha hb hne
  paired : ∀ v hv, σ v ≠ v → ∃ a b ha hb hne,
    F v hv = .complex a b ha hb hne ∧
      F (σ v) (nonleaf_reflect T σ v hv) =
        .complex (σ a) (σ b) ((apply_covBy_apply_iff σ).mpr ha)
          ((apply_covBy_apply_iff σ).mpr hb) (σ.injective.ne hne)

section Recursion

variable (F : Frames T) (hF : Compatible T σ F)

include hF

theorem center_real_of_fixed (p : T → ℂ) (v : T) (hv : ¬IsMax v) (hs : σ v = v) :
    conj (center T F v p) = center T F v p := by
  rcases hF.stable v hv hs with ⟨a, ha, hf⟩ | ⟨a, b, ha, hb, hne, hf⟩
  · rw [center_stableHeight T F v a hv ha hf]
    exact Complex.conj_ofReal _
  · rw [center_stableRealPair T F v a b hv ha hb hne hf]
    exact Complex.conj_ofReal _

/-- Upward finite recursion, using reflection only at leaves. No positivity
or reflection assumption on internal input entries occurs. -/
theorem center_reflection (p : T → ℂ) (hp : ∀ v, IsMax v → p (σ v) = conj (p v)) (v : T) :
    center T F (σ v) p = conj (center T F v p) := by
  induction v using WellFoundedGT.induction with
  | ind v ih =>
    by_cases hv : IsMax v
    · rw [center_leaf T F _ (σ.isMax_apply.mpr hv), center_leaf T F v hv, hp v hv]
    · by_cases hs : σ v = v
      · rw [hs]
        exact (center_real_of_fixed T σ F hF p v hv hs).symm
      · obtain ⟨a, b, ha, hb, hne, hf, hrf⟩ := hF.paired v hv hs
        rw [center_complex T F v a b hv ha hb hne hf,
          center_complex T F (σ v) (σ a) (σ b) (nonleaf_reflect T σ v hv)
            ((apply_covBy_apply_iff σ).mpr ha) ((apply_covBy_apply_iff σ).mpr hb)
              (σ.injective.ne hne) hrf]
        exact ih a ha.lt

theorem radius_reflection (p : T → ℂ) (hp : ∀ v, IsMax v → p (σ v) = conj (p v)) (v : T) :
    radius T F p (σ v) = radius T F p v := by
  by_cases hv : IsMax v
  · simp [radius, hv, σ.isMax_apply.mpr hv]
  · by_cases hs : σ v = v
    · rw [hs]
    · obtain ⟨a, b, ha, hb, hne, hf, hrf⟩ := hF.paired v hv hs
      rw [radius_nonleaf T F p v hv, radius_nonleaf T F p (σ v) (nonleaf_reflect T σ v hv), hf, hrf]
      simp only [Frame.radius, MarkedClusterRescaling.pairRadius, centers_apply,
        center_reflection T σ F hF p hp, ← map_sub, Complex.norm_conj]

theorem localRadii_reflection (p : T → ℂ) (hp : ∀ v, IsMax v → p (σ v) = conj (p v)) (v : T) :
    localRadii T F p (σ v) = localRadii T F p v := by
  simp only [localRadii, ForestNormalizationTelescope.localRadius, ← σ.map_pred,
    radius_reflection T σ F hF p hp]

theorem increments_reflection (p : T → ℂ) (hp : ∀ v, IsMax v → p (σ v) = conj (p v)) (v : T) :
    increments T F p (σ v) = conj (increments T F p v) := by
  simp only [increments, ForestNormalizationTelescope.localIncrement, centers_apply,
    ← σ.map_pred, radius_reflection T σ F hF p hp, center_reflection T σ F hF p hp,
    Complex.real_smul, map_mul, Complex.conj_ofReal, map_sub]

theorem fixedLocalRadii_reflection (p : T → ℂ) (hp : ∀ v, IsMax v → p (σ v) = conj (p v)) (v : T) :
    ForestLeafRadii.fixLeaves T (localRadii T F p) (σ v) =
      ForestLeafRadii.fixLeaves T (localRadii T F p) v := by
  simp only [ForestLeafRadii.fixLeaves, σ.isMax_apply, localRadii_reflection T σ F hF p hp]

end Recursion

/-- The actual real linear reflected parameter subspace. -/
def parameterSubmodule : Submodule ℝ ((T → ℝ) × (T → ℂ)) where
  carrier := {y | (∀ v, y.1 (σ v) = y.1 v) ∧ (∀ v, y.2 (σ v) = conj (y.2 v))}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨har, haa⟩ ⟨hbr, hba⟩
    constructor
    · intro v
      change a.1 (σ v) + b.1 (σ v) = a.1 v + b.1 v
      rw [har, hbr]
    · intro v
      change a.2 (σ v) + b.2 (σ v) = conj (a.2 v + b.2 v)
      rw [haa, hba, map_add]
  smul_mem' := by
    rintro r a ⟨har, haa⟩
    constructor
    · intro v
      change r • a.1 (σ v) = r • a.1 v
      rw [har]
    · intro v
      change r • a.2 (σ v) = conj (r • a.2 v)
      rw [haa]
      simp only [Complex.real_smul, map_mul, Complex.conj_ofReal]

omit [Fintype T] in
theorem mem_parameterSubmodule (y : (T → ℝ) × (T → ℂ)) :
    y ∈ parameterSubmodule T σ ↔
      (∀ v, y.1 (σ v) = y.1 v) ∧ (∀ v, y.2 (σ v) = conj (y.2 v)) := Iff.rfl

omit [Fintype T] in
theorem isClosed_parameterSubmodule : IsClosed (parameterSubmodule T σ : Set ((T → ℝ) × (T → ℂ))) := by
  change IsClosed {y : (T → ℝ) × (T → ℂ) |
    (∀ v, y.1 (σ v) = y.1 v) ∧ (∀ v, y.2 (σ v) = conj (y.2 v))}
  have hr : IsClosed {y : (T → ℝ) × (T → ℂ) | ∀ v, y.1 (σ v) = y.1 v} := by
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro v
    exact isClosed_eq (by fun_prop) (by fun_prop)
  have ha : IsClosed {y : (T → ℝ) × (T → ℂ) | ∀ v, y.2 (σ v) = conj (y.2 v)} := by
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro v
    exact isClosed_eq (by fun_prop) (by fun_prop)
  exact hr.inter ha

theorem parameters_mem (F : Frames T) (hF : Compatible T σ F)
    (p : T → ℂ) (hp : ∀ v, IsMax v → p (σ v) = conj (p v)) :
    (ForestLeafRadii.fixLeaves T (localRadii T F p), increments T F p) ∈ parameterSubmodule T σ :=
  ⟨fixedLocalRadii_reflection T σ F hF p hp, increments_reflection T σ F hF p hp⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestMarkedFrameReflection
