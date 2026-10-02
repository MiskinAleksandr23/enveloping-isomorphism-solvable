import EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedShapeCoordinates

/-! Actual representative selection for finite equivariant sections with
varying constraints in a common topological fiber. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestOrbitSections

open ReflectedShapeCoordinates
open scoped Classical

variable (A : Type*) [Fintype A] (σ : A → A) (hσ : Function.Involutive σ)
variable {E : Type*} [TopologicalSpace E] (κ : E ≃ₜ E) (hκ : Function.Involutive κ)
variable (V : A → Set E) (hV : ∀ a z, z ∈ V a → κ z ∈ V (σ a))

abbrev Sections := {q : A → E // (∀ a, q a ∈ V a) ∧ ∀ a, q (σ a) = κ (q a)}

abbrev Coordinates := ((a : PairRep A σ) → V a.val) ×
  ((a : Fixed A σ) → {z : V a.val // κ z.val = z.val})

def reconstruct (c : Coordinates A σ κ V) (a : A) : E :=
  if hf : σ a = a then (c.2 ⟨a, hf⟩).val.val
  else if hr : IsRep A σ a then (c.1 ⟨a, hr⟩).val
  else κ ((c.1 ⟨σ a, rep_reflection_of_nonfixed A σ hσ hf hr⟩).val)

theorem reconstruct_fixed (c : Coordinates A σ κ V) (a : Fixed A σ) :
    reconstruct A σ hσ κ V c a.val = (c.2 a).val.val := by
  simp only [reconstruct, dif_pos a.property]

theorem reconstruct_rep (c : Coordinates A σ κ V) (a : PairRep A σ) :
    reconstruct A σ hσ κ V c a.val = (c.1 a).val := by
  simp only [reconstruct, dif_neg (rep_not_fixed A σ a.property), dif_pos a.property]

theorem reconstruct_reflected_rep (c : Coordinates A σ κ V) (a : PairRep A σ) :
    reconstruct A σ hσ κ V c (σ a.val) = κ ((c.1 a).val) := by
  have hf : σ (σ a.val) ≠ σ a.val := hσ.injective.ne (rep_not_fixed A σ a.property)
  rw [reconstruct, dif_neg hf, dif_neg (not_rep_reflection A σ hσ a.property)]
  apply congrArg κ
  exact congrArg (fun b : PairRep A σ => (c.1 b).val) (Subtype.ext (hσ a.val))

include hV in
theorem reconstruct_mem (c : Coordinates A σ κ V) (a : A) : reconstruct A σ hσ κ V c a ∈ V a := by
  rcases label_cases A σ hσ a with hf | hr | hr
  · rw [reconstruct_fixed A σ hσ κ V c ⟨a, hf⟩]
    exact (c.2 ⟨a, hf⟩).val.property
  · rw [reconstruct_rep A σ hσ κ V c ⟨a, hr⟩]
    exact (c.1 ⟨a, hr⟩).property
  · have he := reconstruct_reflected_rep A σ hσ κ V c ⟨σ a, hr⟩
    rw [hσ a] at he
    rw [he]
    simpa only [hσ a] using hV (σ a) _ (c.1 ⟨σ a, hr⟩).property

include hκ in
theorem reconstruct_equivariant (c : Coordinates A σ κ V) (a : A) :
    reconstruct A σ hσ κ V c (σ a) = κ (reconstruct A σ hσ κ V c a) := by
  rcases label_cases A σ hσ a with hf | hr | hr
  · rw [hf, reconstruct_fixed A σ hσ κ V c ⟨a, hf⟩]
    exact (c.2 ⟨a, hf⟩).property.symm
  · rw [reconstruct_rep A σ hσ κ V c ⟨a, hr⟩, reconstruct_reflected_rep A σ hσ κ V c ⟨a, hr⟩]
  · have he := reconstruct_reflected_rep A σ hσ κ V c ⟨σ a, hr⟩
    rw [hσ a] at he
    rw [he, reconstruct_rep A σ hσ κ V c ⟨σ a, hr⟩, hκ]

def select (q : Sections A σ κ V) : Coordinates A σ κ V :=
  (fun a => ⟨q.val a.val, q.property.1 a.val⟩,
    fun a => ⟨⟨q.val a.val, q.property.1 a.val⟩,
      (q.property.2 a.val).symm.trans (congrArg q.val a.property)⟩)

def restore (c : Coordinates A σ κ V) : Sections A σ κ V :=
  ⟨reconstruct A σ hσ κ V c, reconstruct_mem A σ hσ κ V hV c,
    reconstruct_equivariant A σ hσ κ hκ V c⟩

theorem restore_select (q : Sections A σ κ V) : restore A σ hσ κ hκ V hV (select A σ κ V q) = q := by
  apply Subtype.ext
  funext a
  change reconstruct A σ hσ κ V (select A σ κ V q) a = q.val a
  rcases label_cases A σ hσ a with hf | hr | hr
  · exact reconstruct_fixed A σ hσ κ V _ ⟨a, hf⟩
  · exact reconstruct_rep A σ hσ κ V _ ⟨a, hr⟩
  · have he := reconstruct_reflected_rep A σ hσ κ V (select A σ κ V q) ⟨σ a, hr⟩
    rw [hσ a] at he
    rw [he]
    exact (q.property.2 (σ a)).symm.trans (congrArg q.val (hσ a))

theorem select_restore (c : Coordinates A σ κ V) : select A σ κ V (restore A σ hσ κ hκ V hV c) = c := by
  apply Prod.ext
  · funext a
    apply Subtype.ext
    exact reconstruct_rep A σ hσ κ V c a
  · funext a
    apply Subtype.ext
    apply Subtype.ext
    exact reconstruct_fixed A σ hσ κ V c a

theorem continuous_select : Continuous (select A σ κ V) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro a
    exact ((continuous_apply a.val).comp continuous_subtype_val).subtype_mk _
  · apply continuous_pi
    intro a
    exact (((continuous_apply a.val).comp continuous_subtype_val).subtype_mk _).subtype_mk _

theorem continuous_restore : Continuous (restore A σ hσ κ hκ V hV) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro a
  unfold reconstruct
  split_ifs <;> fun_prop

/-- Explicit selection and reconstruction prove the factorization. -/
def homeomorph : Sections A σ κ V ≃ₜ Coordinates A σ κ V where
  toEquiv :=
    { toFun := select A σ κ V
      invFun := restore A σ hσ κ hκ V hV
      left_inv := restore_select A σ hσ κ hκ V hV
      right_inv := select_restore A σ hσ κ hκ V hV }
  continuous_toFun := continuous_select A σ κ V
  continuous_invFun := continuous_restore A σ hσ κ hκ V hV

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestOrbitSections
