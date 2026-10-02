import EnvelopingIsomorphism.Deformation.Kontsevich.ForestParameterProduct
import Mathlib.Topology.Homeomorph.Lemmas

/-! Independent real and complex coordinates for actual finite conjugate-reflected arrays. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedShapeCoordinates

open ComplexConjugate
open scoped Classical Topology

variable (A : Type*) [Fintype A] (σ : A → A) (hσ : Function.Involutive σ)

/-- A finite label code used only for selecting orbit representatives, without
introducing or replacing an order on the child labels or their parent tree. -/
def code (u : A) : ℕ := (Fintype.equivFin A u).val

theorem code_injective : Function.Injective (code A) :=
  fun _ _ h => (Fintype.equivFin A).injective (Fin.ext h)

/-- One representative of each nonfixed conjugate pair. -/
def IsRep (u : A) : Prop := code A u < code A (σ u)

abbrev PairRep := {u : A // IsRep A σ u}
abbrev Fixed := {u : A // σ u = u}

/-- The actual reflected array space; no distinctness or half-plane inequalities are imposed. -/
abbrev Space := {q : A → ℂ // ∀ u, q (σ u) = conj (q u)}

abbrev Coordinates := (PairRep A σ → ℂ) × (Fixed A σ → ℝ)

theorem rep_not_fixed {u : A} (hu : IsRep A σ u) : σ u ≠ u := by
  intro h
  simp only [IsRep, h, lt_self_iff_false] at hu

include hσ in
theorem not_rep_reflection {u : A} (hu : IsRep A σ u) : ¬ IsRep A σ (σ u) := by
  change ¬ code A (σ u) < code A (σ (σ u))
  rw [hσ u]
  exact (lt_asymm hu)

include hσ in
theorem rep_reflection_of_nonfixed {u : A} (hf : σ u ≠ u) (hu : ¬ IsRep A σ u) :
    IsRep A σ (σ u) := by
  have hn : code A u ≠ code A (σ u) := (code_injective A).ne hf.symm
  change code A (σ u) < code A (σ (σ u))
  rw [hσ u]
  exact lt_of_le_of_ne (le_of_not_gt hu) hn.symm

include hσ in
theorem label_cases (u : A) : σ u = u ∨ IsRep A σ u ∨ IsRep A σ (σ u) := by
  by_cases hf : σ u = u
  · exact Or.inl hf
  · by_cases hu : IsRep A σ u
    · exact Or.inr (Or.inl hu)
    · exact Or.inr (Or.inr (rep_reflection_of_nonfixed A σ hσ hf hu))

/-- Actual reconstruction uses the chosen complex coordinate and its conjugate;
fixed labels use their real coordinate embedded into ℂ. -/
def reconstruct (c : Coordinates A σ) (u : A) : ℂ :=
  if hf : σ u = u then (c.2 ⟨u, hf⟩ : ℂ)
  else if hu : IsRep A σ u then c.1 ⟨u, hu⟩
  else conj (c.1 ⟨σ u, rep_reflection_of_nonfixed A σ hσ hf hu⟩)

@[simp] theorem reconstruct_fixed (c : Coordinates A σ) (u : Fixed A σ) :
    reconstruct A σ hσ c u.val = (c.2 u : ℂ) := by
  simp only [reconstruct, dif_pos u.property]

@[simp] theorem reconstruct_rep (c : Coordinates A σ) (u : PairRep A σ) :
    reconstruct A σ hσ c u.val = c.1 u := by
  simp only [reconstruct, dif_neg (rep_not_fixed A σ u.property), dif_pos u.property]

@[simp] theorem reconstruct_reflected_rep (c : Coordinates A σ) (u : PairRep A σ) :
    reconstruct A σ hσ c (σ u.val) = conj (c.1 u) := by
  have hf : σ (σ u.val) ≠ σ u.val := hσ.injective.ne (rep_not_fixed A σ u.property)
  rw [reconstruct, dif_neg hf, dif_neg (not_rep_reflection A σ hσ u.property)]
  apply congrArg conj
  apply congrArg c.1
  exact Subtype.ext (hσ u.val)

theorem reconstruct_reflection (c : Coordinates A σ) (u : A) :
    reconstruct A σ hσ c (σ u) = conj (reconstruct A σ hσ c u) := by
  rcases label_cases A σ hσ u with hf | hu | hu
  · have h := reconstruct_fixed A σ hσ c ⟨u, hf⟩
    rw [hf, h]
    simp
  · rw [reconstruct_rep A σ hσ c ⟨u, hu⟩,
      reconstruct_reflected_rep A σ hσ c ⟨u, hu⟩]
  · have h := reconstruct_reflected_rep A σ hσ c ⟨σ u, hu⟩
    rw [hσ u] at h
    rw [h, reconstruct_rep A σ hσ c ⟨σ u, hu⟩]
    simp

/-- Extract the representative values and real values at fixed labels. -/
def coordinates (q : Space A σ) : Coordinates A σ :=
  (fun u => q.val u.val, fun u => (q.val u.val).re)

def ofCoordinates (c : Coordinates A σ) : Space A σ :=
  ⟨reconstruct A σ hσ c, reconstruct_reflection A σ hσ c⟩

omit [Fintype A] in
theorem fixed_value_real (q : Space A σ) (u : Fixed A σ) :
    ((q.val u.val).re : ℂ) = q.val u.val := by
  have hc : conj (q.val u.val) = q.val u.val := by
    simpa only [u.property] using (q.property u.val).symm
  have hi := Complex.conj_eq_iff_im.mp hc
  exact Complex.ext (by simp) (by simpa using hi.symm)

theorem ofCoordinates_coordinates (q : Space A σ) : ofCoordinates A σ hσ (coordinates A σ q) = q := by
  apply Subtype.ext
  funext u
  change reconstruct A σ hσ (coordinates A σ q) u = q.val u
  rcases label_cases A σ hσ u with hf | hu | hu
  · rw [reconstruct_fixed A σ hσ _ ⟨u, hf⟩]
    exact fixed_value_real A σ q ⟨u, hf⟩
  · exact reconstruct_rep A σ hσ _ ⟨u, hu⟩
  · have h := reconstruct_reflected_rep A σ hσ (coordinates A σ q) ⟨σ u, hu⟩
    rw [hσ u] at h
    rw [h]
    exact (q.property (σ u)).symm.trans (congrArg q.val (hσ u))

theorem coordinates_ofCoordinates (c : Coordinates A σ) : coordinates A σ (ofCoordinates A σ hσ c) = c := by
  apply Prod.ext
  · funext u
    exact reconstruct_rep A σ hσ c u
  · funext u
    change (reconstruct A σ hσ c u.val).re = c.2 u
    rw [reconstruct_fixed]
    simp

theorem continuous_coordinates : Continuous (coordinates A σ) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro u
    exact (continuous_apply u.val).comp continuous_subtype_val
  · apply continuous_pi
    intro u
    exact Complex.continuous_re.comp ((continuous_apply u.val).comp continuous_subtype_val)

theorem continuous_ofCoordinates : Continuous (ofCoordinates A σ hσ) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro u
  change Continuous (fun c : Coordinates A σ => reconstruct A σ hσ c u)
  unfold reconstruct
  split_ifs <;> fun_prop

/-- Actual product coordinates, one ℂ per conjugate pair and one ℝ per fixed child. -/
def coordinatesHomeomorph : Space A σ ≃ₜ Coordinates A σ where
  toEquiv :=
    { toFun := coordinates A σ
      invFun := ofCoordinates A σ hσ
      left_inv := ofCoordinates_coordinates A σ hσ
      right_inv := coordinates_ofCoordinates A σ hσ }
  continuous_toFun := continuous_coordinates A σ
  continuous_invFun := continuous_ofCoordinates A σ hσ

end EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedShapeCoordinates
