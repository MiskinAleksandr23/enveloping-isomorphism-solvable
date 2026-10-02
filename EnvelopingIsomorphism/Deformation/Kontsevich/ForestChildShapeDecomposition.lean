import EnvelopingIsomorphism.Deformation.Kontsevich.ForestParameterProduct

/-! Actual global decomposition of root-zero increments into the child arrays
at every nonleaf native parent. The inverse uses the unique predecessor of
each nonroot node; no branching or nontrivial-tree premise is required. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestChildShapeDecomposition

open ForestMarkedFrames ForestParameterProduct ComplexConjugate
open scoped Classical Topology

variable (T : RootedTree)

abbrev Parent := {v : T // ¬IsMax v}
abbrev Child (v : T) := {u : T // v ⋖ u}
abbrev Components := (v : Parent T) → Child T v.val → ℂ

def rootZero : Submodule ℂ (T → ℂ) where
  carrier := {a | a ⊥ = 0}
  zero_mem' := rfl
  add_mem' := by intro a b ha hb; change a ⊥ + b ⊥ = 0; rw [ha, hb, zero_add]
  smul_mem' := by intro r a ha; change r • a ⊥ = 0; rw [ha, smul_zero]

def decompose (a : rootZero T) : Components T := fun _ u => a.val u.val

def predecessorParent (u : T) (hu : u ≠ ⊥) : Parent T :=
  ⟨Order.pred u, not_isMax_of_lt (Order.pred_lt_iff_ne_bot.mpr hu)⟩

def predecessorChild (u : T) (hu : u ≠ ⊥) : Child T (predecessorParent T u hu).val :=
  ⟨u, Order.pred_covBy_of_not_isMin (not_isMin_iff_ne_bot.mpr hu)⟩

def restoreArray (q : Components T) (u : T) : ℂ :=
  if hu : u = ⊥ then 0 else q (predecessorParent T u hu) (predecessorChild T u hu)

@[simp] theorem restoreArray_root (q : Components T) : restoreArray T q ⊥ = 0 := by simp [restoreArray]

def restore (q : Components T) : rootZero T := ⟨restoreArray T q, restoreArray_root T q⟩

theorem restore_decompose (a : rootZero T) : restore T (decompose T a) = a := by
  apply Subtype.ext
  funext u
  by_cases hu : u = ⊥
  · subst u
    exact (restoreArray_root T _).trans a.property.symm
  · simp only [restore, restoreArray, dif_neg hu, decompose, predecessorChild]

theorem decompose_restore (q : Components T) : decompose T (restore T q) = q := by
  funext v u
  rcases v with ⟨v, hv⟩
  rcases u with ⟨u, hu⟩
  have hun : u ≠ ⊥ := ne_of_gt (lt_of_le_of_lt bot_le hu.lt)
  have hp := hu.pred_eq
  dsimp only at hp
  subst v
  simp only [decompose, restore, restoreArray, dif_neg hun, predecessorParent, predecessorChild]

theorem restore_child (q : Components T) (v : Parent T) (u : Child T v.val) :
    (restore T q).val u.val = q v u :=
  congrFun (congrFun (decompose_restore T q) v) u

/-- Every nonroot node occurs in exactly one child array, its actual parent's. -/
def childLinearEquiv : rootZero T ≃ₗ[ℂ] Components T where
  toFun := decompose T
  invFun := restore T
  left_inv := restore_decompose T
  right_inv := decompose_restore T
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem continuous_decompose : Continuous (decompose T) := by
  apply continuous_pi
  intro v
  apply continuous_pi
  intro u
  exact (continuous_apply u.val).comp continuous_subtype_val

theorem continuous_restore : Continuous (restore T) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro u
  change Continuous (fun q => restoreArray T q u)
  unfold restoreArray
  split_ifs
  · exact continuous_const
  · exact (continuous_apply _).comp (continuous_apply _)

/-- Genuine complex continuous-linear product decomposition, also for the
singleton-root tree, where the dependent product has no parent factors. -/
def childContinuousLinearEquiv : rootZero T ≃L[ℂ] Components T where
  toLinearEquiv := childLinearEquiv T
  continuous_toFun := continuous_decompose T
  continuous_invFun := continuous_restore T

@[simp] theorem childContinuousLinearEquiv_apply (a : rootZero T) (v : Parent T) (u : Child T v.val) :
    childContinuousLinearEquiv T a v u = a.val u.val := rfl

variable (F : Frames T)

/-- Literal frame equations on one actual parent-child component. -/
def NodeNormalized (v : Parent T) (q : Child T v.val → ℂ) : Prop :=
  match F v.val v.property with
  | .complex b c hb hc _ => q ⟨b, hb⟩ = 0 ∧ ‖q ⟨c, hc⟩‖ = 1
  | .stableHeight b hb => q ⟨b, hb⟩ = Complex.I
  | .stableRealPair b c hb hc _ => q ⟨b, hb⟩ = 0 ∧ q ⟨c, hc⟩ = 1

def ComponentsNormalized (q : Components T) : Prop := ∀ v, NodeNormalized T F v (q v)

theorem shapeNormalized_iff (a : rootZero T) :
    ShapeNormalized T F a.val ↔ ComponentsNormalized T F (decompose T a) := by
  constructor
  · intro h v
    cases hf : F v.val v.property <;> simpa only [NodeNormalized, decompose, hf] using h v.val v.property
  · intro h v hv
    cases hf : F v hv <;> simpa only [NodeNormalized, decompose, hf] using h ⟨v, hv⟩

variable (σ : T ≃o T)

def reflectParent (v : Parent T) : Parent T :=
  ⟨σ v.val, fun h => v.property (σ.isMax_apply.mp h)⟩

@[simp] theorem reflectParent_val (v : Parent T) : (reflectParent T σ v).val = σ v.val := rfl

theorem reflectParent_involutive (hσ : Function.Involutive σ) : Function.Involutive (reflectParent T σ) :=
  fun v => Subtype.ext (hσ v.val)

def reflectChild (v : Parent T) (u : Child T v.val) : Child T (reflectParent T σ v).val :=
  ⟨σ u.val, (apply_covBy_apply_iff σ).mpr u.property⟩

@[simp] theorem reflectChild_val (v : Parent T) (u : Child T v.val) : (reflectChild T σ v u).val = σ u.val := rfl

def ComponentsReflection (q : Components T) : Prop :=
  ∀ (v : Parent T) (u : Child T v.val), q (reflectParent T σ v) (reflectChild T σ v u) = conj (q v u)

theorem reflection_iff (a : rootZero T) :
    (∀ u, a.val (σ u) = conj (a.val u)) ↔ ComponentsReflection T σ (decompose T a) := by
  constructor
  · intro h v u
    exact h u.val
  · intro h u
    by_cases hu : u = ⊥
    · subst u
      rw [σ.map_bot, a.property, map_zero]
    · exact h (predecessorParent T u hu) (predecessorChild T u hu)

theorem shapeConstraints_iff (a : rootZero T) :
    ShapeConstraints T σ F a.val ↔
      ComponentsNormalized T F (decompose T a) ∧ ComponentsReflection T σ (decompose T a) := by
  constructor
  · rintro ⟨hn, hr, _⟩
    exact ⟨(shapeNormalized_iff T F a).mp hn, (reflection_iff T σ a).mp hr⟩
  · rintro ⟨hn, hr⟩
    exact ⟨(shapeNormalized_iff T F a).mpr hn, (reflection_iff T σ a).mpr hr, a.property⟩

abbrev ComponentShapeSpace := {q : Components T // ComponentsNormalized T F q ∧ ComponentsReflection T σ q}

def shapeDecompose (a : ShapeSpace T σ F) : ComponentShapeSpace T F σ :=
  ⟨decompose T ⟨a.val, a.property.2.2⟩, (shapeConstraints_iff T F σ _).mp a.property⟩

def shapeRestore (q : ComponentShapeSpace T F σ) : ShapeSpace T σ F :=
  ⟨(restore T q.val).val, (shapeConstraints_iff T F σ _).mpr (by
    rw [decompose_restore]
    exact q.property)⟩

/-- Actual normalized global ShapeSpace, with every reflection relation
retained, is homeomorphic to its native parent-child component space. -/
def shapeHomeomorph : ShapeSpace T σ F ≃ₜ ComponentShapeSpace T F σ where
  toEquiv :=
    { toFun := shapeDecompose T F σ
      invFun := shapeRestore T F σ
      left_inv := by
        intro a
        apply Subtype.ext
        change (restore T (decompose T ⟨a.val, a.property.2.2⟩)).val = a.val
        exact congrArg Subtype.val (restore_decompose T ⟨a.val, a.property.2.2⟩)
      right_inv := by
        intro q
        apply Subtype.ext
        exact decompose_restore T q.val }
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro v
    apply continuous_pi
    intro u
    exact (continuous_apply u.val).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp ((continuous_restore T).comp continuous_subtype_val)

/-- At a fixed parent, reflection restricts to its actual native children. -/
def stableChildReflection (v : T) (hv : σ v = v) : Child T v → Child T v :=
  fun u => ⟨σ u.val, by simpa only [hv] using (apply_covBy_apply_iff σ).mpr u.property⟩

theorem stableChildReflection_involutive (hσ : Function.Involutive σ) (v : T) (hv : σ v = v) :
    Function.Involutive (stableChildReflection T σ v hv) := fun u => Subtype.ext (hσ u.val)

theorem component_reflection_at_fixed (q : Components T) (hq : ComponentsReflection T σ q)
    (v : Parent T) (hv : σ v.val = v.val) (u : Child T v.val) :
    q v (stableChildReflection T σ v.val hv u) = conj (q v u) := by
  have hr : ∀ u, (restore T q).val (σ u) = conj ((restore T q).val u) :=
    (reflection_iff T σ (restore T q)).mpr (by rw [decompose_restore]; exact hq)
  have h := hr u.val
  rw [restore_child T q v u] at h
  exact (restore_child T q v (stableChildReflection T σ v.val hv u)).symm.trans h

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestChildShapeDecomposition
