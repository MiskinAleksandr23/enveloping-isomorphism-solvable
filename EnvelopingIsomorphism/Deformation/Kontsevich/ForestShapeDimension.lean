import EnvelopingIsomorphism.Deformation.Kontsevich.ForestShapeCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestDimensionCount

/-! Exact finite counts for the actual reflected forest shape model. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestShapeDimension

open ReflectedShapeCoordinates ForestChildShapeDecomposition ForestShapeCoordinates
open scoped Classical BigOperators

section Involution

variable (A : Type*) [Fintype A] (σ : A → A) (hσ : Function.Involutive σ)

def labelSplit (a : A) : Fixed A σ ⊕ (PairRep A σ × Bool) :=
  if hf : σ a = a then Sum.inl ⟨a, hf⟩ else
    if hr : IsRep A σ a then Sum.inr (⟨a, hr⟩, false) else
      Sum.inr (⟨σ a, rep_reflection_of_nonfixed A σ hσ hf hr⟩, true)

def labelMerge : Fixed A σ ⊕ (PairRep A σ × Bool) → A
  | Sum.inl a => a.val
  | Sum.inr (a, b) => if b then σ a.val else a.val

theorem merge_split (a : A) : labelMerge A σ (labelSplit A σ hσ a) = a := by
  unfold labelSplit
  split_ifs <;> simp [labelMerge, hσ a]

theorem split_merge (a : Fixed A σ ⊕ (PairRep A σ × Bool)) :
    labelSplit A σ hσ (labelMerge A σ a) = a := by
  rcases a with a | ⟨a, b⟩
  · simp only [labelMerge, labelSplit, dif_pos a.property]
  · cases b
    · simp only [labelMerge, Bool.false_eq_true, ↓reduceIte, labelSplit,
        dif_neg (rep_not_fixed A σ a.property), dif_pos a.property]
    · have hf : σ (σ a.val) ≠ σ a.val := hσ.injective.ne (rep_not_fixed A σ a.property)
      simp only [labelMerge, ↓reduceIte, labelSplit, dif_neg hf,
        dif_neg (not_rep_reflection A σ hσ a.property)]
      congr 2
      exact Subtype.ext (hσ a.val)

def labelEquiv : A ≃ Fixed A σ ⊕ (PairRep A σ × Bool) where
  toFun := labelSplit A σ hσ
  invFun := labelMerge A σ
  left_inv := merge_split A σ hσ
  right_inv := split_merge A σ hσ

include hσ in
theorem card_involution : Fintype.card A = Fintype.card (Fixed A σ) + 2 * Fintype.card (PairRep A σ) := by
  simpa only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, mul_comm] using
    Fintype.card_congr (labelEquiv A σ hσ)

include hσ in
theorem sum_invariant [Fintype (Fixed A σ)] [Fintype (PairRep A σ)]
    {M : Type*} [AddCommMonoid M] (f : A → M) (hf : ∀ a, f (σ a) = f a) :
    (∑ a, f a) = (∑ a : Fixed A σ, f a.val) + ∑ a : PairRep A σ, (f a.val + f a.val) := by
  have he := Fintype.sum_equiv (labelEquiv A σ hσ).symm
    (fun a : Fixed A σ ⊕ (PairRep A σ × Bool) => f (labelMerge A σ a)) f (fun _ => rfl)
  simpa only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool,
    labelMerge, Bool.false_eq_true, ↓reduceIte, hf] using he.symm

def representativeLabel : Fixed A σ ⊕ PairRep A σ → A := Sum.elim Subtype.val Subtype.val

include hσ in
theorem representative_quotient_bijective (S : Setoid A)
    (hS : ∀ a b, S.r a b ↔ a = b ∨ σ a = b) :
    Function.Bijective (fun a : Fixed A σ ⊕ PairRep A σ => Quotient.mk S (representativeLabel A σ a)) := by
  constructor
  · intro a b hab
    have h := (hS _ _).mp (Quotient.exact hab)
    rcases a with a | a <;> rcases b with b | b <;>
      simp only [representativeLabel, Sum.elim_inl, Sum.elim_inr] at h
    · apply congrArg Sum.inl
      apply Subtype.ext
      rcases h with h | h
      · exact h
      · exact a.property.symm.trans h
    · exfalso
      apply rep_not_fixed A σ b.property
      rcases h with h | h
      · rw [← h, a.property]
      · rw [a.property] at h
        rw [← h, a.property]
    · exfalso
      apply rep_not_fixed A σ a.property
      rcases h with h | h
      · rw [h, b.property]
      · have hh := congrArg σ h
        rw [hσ, b.property] at hh
        exact h.trans hh.symm
    · apply congrArg Sum.inr
      apply Subtype.ext
      rcases h with h | h
      · exact h
      · exact False.elim ((not_rep_reflection A σ hσ a.property) (h ▸ b.property))
  · intro q
    induction q using Quotient.inductionOn with
    | h a =>
      rcases label_cases A σ hσ a with hf | hr | hr
      · exact ⟨Sum.inl ⟨a, hf⟩, rfl⟩
      · exact ⟨Sum.inr ⟨a, hr⟩, rfl⟩
      · refine ⟨Sum.inr ⟨σ a, hr⟩, Quotient.sound ((hS _ _).mpr (Or.inr (hσ a)))⟩

include hσ in
theorem card_quotient (S : Setoid A) [Fintype (Quotient S)]
    (hS : ∀ a b, S.r a b ↔ a = b ∨ σ a = b) :
    Fintype.card (Quotient S) = Fintype.card (Fixed A σ) + Fintype.card (PairRep A σ) := by
  simpa only [Fintype.card_sum] using
    (Fintype.card_congr (Equiv.ofBijective _ (representative_quotient_bijective A σ hσ S hS))).symm

include hσ in
theorem twice_card_quotient (S : Setoid A) [Fintype (Quotient S)]
    (hS : ∀ a b, S.r a b ↔ a = b ∨ σ a = b) :
    2 * Fintype.card (Quotient S) = Fintype.card A + Fintype.card (Fixed A σ) := by
  rw [card_quotient A σ hσ S hS, card_involution A σ hσ]
  omega

include hσ in
theorem reflectedRealIndex_card : Fintype.card (ForestFiniteCoordinateProducts.ReflectedRealIndex A σ) = Fintype.card A := by
  simp only [ForestFiniteCoordinateProducts.ReflectedRealIndex, Fintype.card_sum, Fintype.card_prod, Fintype.card_bool]
  have h := card_involution A σ hσ
  omega

end Involution

section FreeChildren

variable (A : Type*) [Fintype A] (a b : A) (hab : a ≠ b)

include hab in
theorem freePair_card : Fintype.card {u : A // u ≠ a ∧ u ≠ b} + 2 = Fintype.card A := by
  have hcard : Fintype.card {u : A // u = a ∨ u = b} = 2 := by
    have he : {u : A // u = a ∨ u = b} ≃ ↥({a, b} : Finset A) :=
      Equiv.subtypeEquivRight (fun u => by simp)
    rw [Fintype.card_congr he, Fintype.card_coe, Finset.card_pair hab]
  have hc := Fintype.card_subtype_compl (fun u : A => u = a ∨ u = b)
  have ht : Fintype.card {u : A // u ≠ a ∧ u ≠ b} = Fintype.card {u : A // ¬(u = a ∨ u = b)} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun u => not_or.symm))
  have hle : 2 ≤ Fintype.card A := by
    rw [← hcard]
    exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  rw [ht, hc, hcard]
  omega

end FreeChildren

section Forest

variable (T : RootedTree) [Fintype T] (σ : T ≃o T) (hσ : Function.Involutive σ)
variable (F : ForestMarkedFrames.Frames T)

def childReflectEquiv (v : Parent T) : Child T v.val ≃ Child T (reflectParent T σ v).val :=
  Equiv.subtypeEquiv σ.toEquiv (fun _ => (apply_covBy_apply_iff σ).symm)

theorem childCard_reflect (v : Parent T) :
    Fintype.card (Child T (reflectParent T σ v).val) = Fintype.card (Child T v.val) :=
  (Fintype.card_congr (childReflectEquiv T σ v)).symm

theorem pairedRealIndex_card (v : PairParent T σ) (M : ComplexMarks T σ F v.val) :
    Fintype.card (PairedRealIndex T σ F v M) + 4 = 2 * Fintype.card (Child T v.val.val) := by
  have h : Fintype.card (ForestNodeShapeCoordinates.ComplexFree (Child T v.val.val) M.a M.b) + 2 =
      Fintype.card (Child T v.val.val) := by
    simpa only [← Nat.card_eq_fintype_card] using freePair_card _ M.a M.b M.ne
  simp only [PairedRealIndex, Fintype.card_prod, Fintype.card_bool]
  omega

theorem stableRealIndex_card (v : FixedParent T σ) (M : StableMarks T σ F v) :
    Fintype.card (StableRealIndex T σ hσ F v M) + 2 = Fintype.card (Child T v.val.val) := by
  letI : DecidableEq (Child T v.val.val) := Classical.decEq _
  cases M with
  | height a ha hf =>
    dsimp only [StableRealIndex]
    have hc := reflectedRealIndex_card
      (ForestNodeShapeCoordinates.HeightFree (Child T v.val.val) (childReflection T σ v) a)
      (ForestNodeShapeCoordinates.heightReflection _ _ (childReflection_involutive T σ hσ v) a)
      (ForestNodeShapeCoordinates.heightReflection_involutive _ _ (childReflection_involutive T σ hσ v) a)
    have hp := freePair_card (Child T v.val.val) a (childReflection T σ v a) ha.symm
    simp only [← Nat.card_eq_fintype_card] at hc hp ⊢
    exact hc ▸ hp
  | realPair a b hne ha hb hf =>
    dsimp only [StableRealIndex]
    have hc := reflectedRealIndex_card (ForestNodeShapeCoordinates.RealPairFree (Child T v.val.val) a b)
      (ForestNodeShapeCoordinates.realPairReflection _ _ (childReflection_involutive T σ hσ v) a b ha hb)
      (ForestNodeShapeCoordinates.realPairReflection_involutive _ _ (childReflection_involutive T σ hσ v) a b ha hb)
    have hp := freePair_card (Child T v.val.val) a b hne
    simp only [← Nat.card_eq_fintype_card] at hc hp ⊢
    exact hc ▸ hp

theorem realCount_relation (P : ∀ v : PairParent T σ, ComplexMarks T σ F v.val)
    (S : ∀ v : FixedParent T σ, StableMarks T σ F v) :
    realCount T σ hσ F P S + 4 * Fintype.card (PairParent T σ) + 2 * Fintype.card (FixedParent T σ) =
      ∑ v : Parent T, Fintype.card (Child T v.val) := by
  have hp : (∑ v : PairParent T σ, (Fintype.card (PairedRealIndex T σ F v (P v)) + 4)) =
      ∑ v : PairParent T σ, 2 * Fintype.card (Child T v.val.val) :=
    Finset.sum_congr rfl (fun v _ => pairedRealIndex_card T σ F v (P v))
  have hs : (∑ v : FixedParent T σ, (Fintype.card (StableRealIndex T σ hσ F v (S v)) + 2)) =
      ∑ v : FixedParent T σ, Fintype.card (Child T v.val.val) :=
    Finset.sum_congr rfl (fun v _ => stableRealIndex_card T σ hσ F v (S v))
  have ht : (∑ v : Parent T, Fintype.card (Child T v.val)) =
      (∑ v : FixedParent T σ, Fintype.card (Child T v.val.val)) +
        ∑ v : PairParent T σ, 2 * Fintype.card (Child T v.val.val) := by
    simpa only [← two_mul] using sum_invariant (Parent T) (reflectParent T σ) (reflectParent_involutive T σ hσ)
      (fun v => Fintype.card (Child T v.val)) (childCard_reflect T σ)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id] at hp hs
  simp only [realCount, RealIndex, Fintype.card_sum, Fintype.card_sigma]
  omega

private theorem card_delete_point (A : Type*) [Fintype A] (a : A) :
    Fintype.card {u : A // u ≠ a} + 1 = Fintype.card A := by
  rw [Fintype.card_subtype_compl (fun u : A => u = a)]
  have hc : Fintype.card {u : A // u = a} = 1 := by simp
  rw [hc]
  have hp : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ⟨a⟩
  omega

def rootParent (hroot : ¬IsMax (⊥ : T)) : Parent T := ⟨⊥, hroot⟩

def rootFixedParent (hroot : ¬IsMax (⊥ : T)) : FixedParent T σ :=
  ⟨rootParent T hroot, Subtype.ext σ.map_bot⟩

def activeParentEquiv (hroot : ¬IsMax (⊥ : T)) :
    ReflectedRadiusCoordinates.ActiveNode T ≃ {v : Parent T // v ≠ rootParent T hroot} where
  toFun u := ⟨⟨u.val, u.property.2⟩, fun h => u.property.1 (congrArg Subtype.val h)⟩
  invFun v := ⟨v.val.val, fun h => v.property (Subtype.ext h), v.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def activeFixedParentEquiv (hroot : ¬IsMax (⊥ : T)) :
    Fixed (ReflectedRadiusCoordinates.ActiveNode T) (ReflectedRadiusCoordinates.reflect T σ) ≃
      {v : FixedParent T σ // v ≠ rootFixedParent T σ hroot} where
  toFun u := ⟨⟨⟨u.val.val, u.val.property.2⟩,
    Subtype.ext (congrArg (fun z : ReflectedRadiusCoordinates.ActiveNode T => z.val) u.property)⟩,
    fun h => u.val.property.1 (congrArg (fun v : FixedParent T σ => v.val.val) h)⟩
  invFun v := ⟨⟨v.val.val.val, fun h => v.property (Subtype.ext (Subtype.ext h)), v.val.val.property⟩,
    Subtype.ext (congrArg (fun z : Parent T => z.val) v.val.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem activeCard_relation (hroot : ¬IsMax (⊥ : T)) :
    Fintype.card (ReflectedRadiusCoordinates.ActiveNode T) + 1 = Fintype.card (Parent T) := by
  rw [Fintype.card_congr (activeParentEquiv T hroot)]
  simpa only [← Nat.card_eq_fintype_card] using card_delete_point (Parent T) (rootParent T hroot)

theorem activeFixedCard_relation (hroot : ¬IsMax (⊥ : T)) :
    Fintype.card (Fixed (ReflectedRadiusCoordinates.ActiveNode T) (ReflectedRadiusCoordinates.reflect T σ)) + 1 =
      Fintype.card (FixedParent T σ) := by
  rw [Fintype.card_congr (activeFixedParentEquiv T σ hroot)]
  simpa only [← Nat.card_eq_fintype_card] using card_delete_point (FixedParent T σ) (rootFixedParent T σ hroot)

include hσ in
theorem radialCount_relation (hroot : ¬IsMax (⊥ : T)) :
    ReflectedRadiusCoordinates.freeRadiusCount T σ hσ + 1 =
      Fintype.card (FixedParent T σ) + Fintype.card (PairParent T σ) := by
  have hq := twice_card_quotient (ReflectedRadiusCoordinates.ActiveNode T)
    (ReflectedRadiusCoordinates.reflect T σ) (ReflectedRadiusCoordinates.reflect_involutive T σ hσ)
    (ReflectedRadiusCoordinates.orbitSetoid T σ hσ) (fun _ _ => Iff.rfl)
  have ha := activeCard_relation T hroot
  have hf := activeFixedCard_relation T σ hroot
  have hp : Fintype.card (Parent T) = Fintype.card (FixedParent T σ) + 2 * Fintype.card (PairParent T σ) :=
    by simpa only [← Nat.card_eq_fintype_card] using
      card_involution (Parent T) (reflectParent T σ) (reflectParent_involutive T σ hσ)
  change 2 * ReflectedRadiusCoordinates.freeRadiusCount T σ hσ = _ at hq
  simp only [← Nat.card_eq_fintype_card] at hq ha hf hp ⊢
  omega

theorem parent_leaf_card : Fintype.card (Parent T) + Fintype.card {u : T // IsMax u} = Fintype.card T := by
  have h := Fintype.card_subtype_compl (IsMax : T → Prop)
  have hl : Fintype.card {u : T // IsMax u} ≤ Fintype.card T :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  change Fintype.card (Parent T) = _ at h
  omega

/-- The actual free model dimension is the number of original doubled leaves
minus two, derived from orbit counts, marked-child deletion, and tree Euler. -/
theorem total_dimension_leaves (hroot : ¬IsMax (⊥ : T))
    (P : ∀ v : PairParent T σ, ComplexMarks T σ F v.val)
    (S : ∀ v : FixedParent T σ, StableMarks T σ F v) :
    ReflectedRadiusCoordinates.freeRadiusCount T σ hσ + circleCount T σ + realCount T σ hσ F P S + 2 =
      Fintype.card {u : T // IsMax u} := by
  have hr := radialCount_relation T σ hσ hroot
  have hs := realCount_relation T σ hσ F P S
  have hp : Fintype.card (Parent T) = Fintype.card (FixedParent T σ) + 2 * Fintype.card (PairParent T σ) :=
    by simpa only [← Nat.card_eq_fintype_card] using
      card_involution (Parent T) (reflectParent T σ) (reflectParent_involutive T σ hσ)
  have hc := ForestDimensionCount.card_children T
  have hl := parent_leaf_card T
  unfold circleCount
  omega

end Forest

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestShapeDimension
