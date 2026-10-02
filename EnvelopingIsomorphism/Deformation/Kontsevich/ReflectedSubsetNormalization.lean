import EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedClusterAnchors
import EnvelopingIsomorphism.Deformation.Kontsevich.SubsetNormalizedLimits
import EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedClusterLimits

/-!
# Actual normalization on all reflected finite subsets

Stable subsets use real centering; pairs of nonstable subsets use complex
centering at the constructed equivariant anchors. The actual normalized arrays
have unit norm and respect reflection across subsets exactly.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedSubsetNormalization

open ComplexConjugate
open SubsetNormalizedLimits (LargeSubset)
open scoped Classical

variable {I : Type*} [Fintype I]

def toNonemptySubset (A : LargeSubset I) : ReflectedClusterAnchors.NonemptySubset I :=
  ⟨A.val, Finset.card_pos.mp (lt_trans Nat.zero_lt_one A.property)⟩

def reflectLargeSubset (σ : I → I) (hσ : Function.Involutive σ) (A : LargeSubset I) : LargeSubset I :=
  ⟨(ReflectedClusterAnchors.reflectSubset σ (toNonemptySubset A)).val, by
    rw [ReflectedClusterAnchors.card_reflectSubset σ hσ]
    exact A.property⟩

@[simp] theorem reflectLargeSubset_val (σ : I → I) (hσ : Function.Involutive σ) (A : LargeSubset I) :
    (reflectLargeSubset σ hσ A).val = A.val.image σ := rfl

@[simp] theorem toNonemptySubset_reflect (σ : I → I) (hσ : Function.Involutive σ) (A : LargeSubset I) :
    toNonemptySubset (reflectLargeSubset σ hσ A) =
      ReflectedClusterAnchors.reflectSubset σ (toNonemptySubset A) := rfl

theorem reflectLargeSubset_involutive (σ : I → I) (hσ : Function.Involutive σ) :
    Function.Involutive (reflectLargeSubset σ hσ) := by
  intro A
  apply Subtype.ext
  exact congrArg (fun B : ReflectedClusterAnchors.NonemptySubset I => B.val)
    (ReflectedClusterAnchors.reflectSubset_involutive σ hσ (toNonemptySubset A))

def reflectIndex (σ : I → I) (hσ : Function.Involutive σ) (A : LargeSubset I)
    (j : A.val) : (reflectLargeSubset σ hσ A).val :=
  ⟨σ j.val, Finset.mem_image.mpr ⟨j.val, j.property, rfl⟩⟩

@[simp] theorem reflectIndex_val (σ : I → I) (hσ : Function.Involutive σ)
    (A : LargeSubset I) (j : A.val) : (reflectIndex σ hσ A j).val = σ j.val := rfl

def reflectIndexEquiv (σ : I → I) (hσ : Function.Involutive σ) (A : LargeSubset I) :
    A.val ≃ (reflectLargeSubset σ hσ A).val where
  toFun := reflectIndex σ hσ A
  invFun := fun j => ⟨σ j.val,
    (ReflectedClusterAnchors.mem_reflectSubset_iff σ hσ (toNonemptySubset A) j.val).mp j.property⟩
  left_inv := fun j => Subtype.ext (hσ j.val)
  right_inv := fun j => Subtype.ext (hσ j.val)

def chosenAnchor (σ : I → I) (hσ : Function.Involutive σ) (A : LargeSubset I) : A.val :=
  ReflectedClusterAnchors.anchor σ hσ (toNonemptySubset A)

def IsStable (σ : I → I) (A : LargeSubset I) : Prop := A.val.image σ = A.val

theorem reflectLargeSubset_eq_of_stable (σ : I → I) (hσ : Function.Involutive σ)
    (A : LargeSubset I) (hA : IsStable σ A) : reflectLargeSubset σ hσ A = A :=
  Subtype.ext hA

theorem isStable_reflect_iff (σ : I → I) (hσ : Function.Involutive σ) (A : LargeSubset I) :
    IsStable σ (reflectLargeSubset σ hσ A) ↔ IsStable σ A := by
  unfold IsStable
  rw [reflectLargeSubset_val, Finset.image_image]
  have hc : σ ∘ σ = id := funext hσ
  rw [hc, Finset.image_id]
  exact eq_comm

theorem chosenAnchor_reflect (σ : I → I) (hσ : Function.Involutive σ)
    (A : LargeSubset I) (hA : ¬IsStable σ A) :
    (chosenAnchor σ hσ (reflectLargeSubset σ hσ A)).val = σ (chosenAnchor σ hσ A).val :=
  ReflectedClusterAnchors.anchor_reflectSubset σ hσ (toNonemptySubset A) hA

def stableReflection (σ : I → I) (A : LargeSubset I) (hA : IsStable σ A) : A.val → A.val :=
  fun j => ⟨σ j.val, by
    exact (congrArg (fun B : Finset I => σ j.val ∈ B) hA).mp
      (Finset.mem_image.mpr ⟨j.val, j.property, rfl⟩)⟩

theorem stableReflection_involutive (σ : I → I) (hσ : Function.Involutive σ)
    (A : LargeSubset I) (hA : IsStable σ A) : Function.Involutive (stableReflection σ A hA) :=
  fun j => Subtype.ext (hσ j.val)

def normalizedOn (σ : I → I) (hσ : Function.Involutive σ) (A : LargeSubset I) (p : I → ℂ) :
    A.val → ℂ :=
  if IsStable σ A then ReflectedClusterLimits.normalized (chosenAnchor σ hσ A) (fun j : A.val => p j)
  else NormalizedClusterLimits.normalized (chosenAnchor σ hσ A) (fun j : A.val => p j)

def radiusOn (σ : I → I) (hσ : Function.Involutive σ) (A : LargeSubset I) (p : I → ℂ) : ℝ :=
  if IsStable σ A then ReflectedClusterLimits.radius (chosenAnchor σ hσ A) (fun j : A.val => p j)
  else NormalizedClusterLimits.radius (chosenAnchor σ hσ A) (fun j : A.val => p j)

def centerOn (σ : I → I) (hσ : Function.Involutive σ) (A : LargeSubset I) (p : I → ℂ) : ℂ :=
  if IsStable σ A then ((p (chosenAnchor σ hσ A)).re : ℂ) else p (chosenAnchor σ hσ A)

theorem radiusOn_eq_norm (σ : I → I) (hσ : Function.Involutive σ) (A : LargeSubset I) (p : I → ℂ) :
    radiusOn σ hσ A p = ‖fun j : A.val => p j - centerOn σ hσ A p‖ := by
  unfold radiusOn centerOn
  split_ifs <;> rfl

theorem normalizedOn_apply (σ : I → I) (hσ : Function.Involutive σ) (A : LargeSubset I)
    (p : I → ℂ) (j : A.val) :
    normalizedOn σ hσ A p j = (radiusOn σ hσ A p)⁻¹ • (p j - centerOn σ hσ A p) := by
  by_cases hA : IsStable σ A <;>
    simp only [normalizedOn, radiusOn, centerOn, hA, if_true, if_false,
      ReflectedClusterLimits.normalized, ReflectedClusterLimits.centered, ReflectedClusterLimits.center,
      NormalizedClusterLimits.normalized, NormalizedClusterLimits.centered, Pi.smul_apply]

theorem radiusOn_pos (σ : I → I) (hσ : Function.Involutive σ) (A : LargeSubset I)
    (p : I → ℂ) (hp : Function.Injective p) : 0 < radiusOn σ hσ A p := by
  unfold radiusOn
  split_ifs
  · exact ReflectedClusterLimits.radius_pos_of_injective _ _ (hp.comp Subtype.val_injective)
  · exact NormalizedClusterLimits.radius_pos_of_injective _ _ (hp.comp Subtype.val_injective)

theorem radiusOn_nonneg (σ : I → I) (hσ : Function.Involutive σ) (A : LargeSubset I) (p : I → ℂ) :
    0 ≤ radiusOn σ hσ A p := by
  rw [radiusOn_eq_norm]
  exact norm_nonneg _

@[simp] theorem normalizedOn_anchor_re (σ : I → I) (hσ : Function.Involutive σ)
    (A : LargeSubset I) (p : I → ℂ) :
    (normalizedOn σ hσ A p (chosenAnchor σ hσ A)).re = 0 := by
  unfold normalizedOn
  split_ifs
  · exact ReflectedClusterLimits.normalized_anchor_re _ _
  · rw [NormalizedClusterLimits.normalized_anchor]
    rfl

theorem normalizedOn_anchor_eq_zero (σ : I → I) (hσ : Function.Involutive σ)
    (A : LargeSubset I) (p : I → ℂ) (hA : ¬IsStable σ A) :
    normalizedOn σ hσ A p (chosenAnchor σ hσ A) = 0 := by
  rw [normalizedOn, if_neg hA]
  exact NormalizedClusterLimits.normalized_anchor _ _

theorem norm_normalizedOn (σ : I → I) (hσ : Function.Involutive σ) (A : LargeSubset I)
    (p : I → ℂ) (hp : Function.Injective p) : ‖normalizedOn σ hσ A p‖ = 1 := by
  unfold normalizedOn
  split_ifs
  · exact ReflectedClusterLimits.norm_normalized _ _
      (ReflectedClusterLimits.radius_pos_of_injective _ _ (hp.comp Subtype.val_injective))
  · exact NormalizedClusterLimits.norm_normalized _ _
      (NormalizedClusterLimits.radius_pos_of_injective _ _ (hp.comp Subtype.val_injective))

theorem normalizedOn_mem_sphere (σ : I → I) (hσ : Function.Involutive σ) (A : LargeSubset I)
    (p : I → ℂ) (hp : Function.Injective p) :
    normalizedOn σ hσ A p ∈ Metric.sphere (0 : A.val → ℂ) 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using norm_normalizedOn σ hσ A p hp

theorem centerOn_mirror (σ : I → I) (hσ : Function.Involutive σ) (A : LargeSubset I)
    (p : I → ℂ) (hp : ∀ j, p (σ j) = conj (p j)) :
    centerOn σ hσ (reflectLargeSubset σ hσ A) p = conj (centerOn σ hσ A p) := by
  by_cases hA : IsStable σ A
  · rw [reflectLargeSubset_eq_of_stable σ hσ A hA]
    simp only [centerOn, if_pos hA, Complex.conj_ofReal]
  · have hRA : ¬IsStable σ (reflectLargeSubset σ hσ A) :=
      fun h => hA ((isStable_reflect_iff σ hσ A).mp h)
    simp only [centerOn, if_neg hRA, if_neg hA, chosenAnchor_reflect σ hσ A hA, hp]

private theorem norm_conj_array {J : Type*} [Fintype J] (f : J → ℂ) :
    ‖fun j => conj (f j)‖ = ‖f‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg f)).mpr
    intro j
    rw [Complex.norm_conj]
    exact norm_le_pi_norm f j
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (fun j => conj (f j)))).mpr
    intro j
    simpa only [Complex.norm_conj] using norm_le_pi_norm (fun j => conj (f j)) j

theorem radiusOn_mirror (σ : I → I) (hσ : Function.Involutive σ) (A : LargeSubset I)
    (p : I → ℂ) (hp : ∀ j, p (σ j) = conj (p j)) :
    radiusOn σ hσ (reflectLargeSubset σ hσ A) p = radiusOn σ hσ A p := by
  let e := reflectIndexEquiv σ hσ A
  rw [radiusOn_eq_norm, radiusOn_eq_norm]
  rw [← e.surjective.pi_norm_comp (fun j => p j - centerOn σ hσ (reflectLargeSubset σ hσ A) p)]
  have heq : (fun j : (reflectLargeSubset σ hσ A).val =>
      p j - centerOn σ hσ (reflectLargeSubset σ hσ A) p) ∘ e =
      fun j : A.val => conj (p j - centerOn σ hσ A p) := by
    funext j
    change p (σ j.val) - centerOn σ hσ (reflectLargeSubset σ hσ A) p = _
    rw [hp, centerOn_mirror σ hσ A p hp, map_sub]
  rw [heq]
  exact norm_conj_array _

/-- Exact cross-subset reflection for the actual mixed normalization. No
injectivity, limit or compact extraction hypothesis is needed for this identity. -/
theorem normalizedOn_mirror (σ : I → I) (hσ : Function.Involutive σ) (A : LargeSubset I)
    (p : I → ℂ) (hp : ∀ j, p (σ j) = conj (p j)) (j : A.val) :
    normalizedOn σ hσ (reflectLargeSubset σ hσ A) p (reflectIndex σ hσ A j) =
      conj (normalizedOn σ hσ A p j) := by
  rw [normalizedOn_apply, normalizedOn_apply, reflectIndex_val, hp,
    centerOn_mirror σ hσ A p hp, radiusOn_mirror σ hσ A p hp]
  simp only [Complex.real_smul, map_mul, map_sub, Complex.conj_ofReal]

theorem normalizedOn_stable_mirror (σ : I → I) (hσ : Function.Involutive σ)
    (A : LargeSubset I) (hA : IsStable σ A) (p : I → ℂ)
    (hp : ∀ j, p (σ j) = conj (p j)) (j : A.val) :
    normalizedOn σ hσ A p (stableReflection σ A hA j) = conj (normalizedOn σ hσ A p j) := by
  rw [normalizedOn, if_pos hA]
  exact ReflectedClusterLimits.normalized_mirror (stableReflection σ A hA)
    (chosenAnchor σ hσ A) (fun j : A.val => p j) (fun j => hp j.val) j

theorem normalizedOn_sub (σ : I → I) (hσ : Function.Involutive σ) (A : LargeSubset I)
    (p : I → ℂ) (j k : A.val) :
    normalizedOn σ hσ A p j - normalizedOn σ hσ A p k =
      (radiusOn σ hσ A p)⁻¹ • (p j - p k) := by
  rw [normalizedOn_apply, normalizedOn_apply, ← smul_sub]
  congr 1
  abel

end EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedSubsetNormalization
