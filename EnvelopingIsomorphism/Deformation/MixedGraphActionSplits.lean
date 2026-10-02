import EnvelopingIsomorphism.Deformation.MixedGraphProfileTensors
import EnvelopingIsomorphism.Deformation.GraphCoefficientProfiles

/-! Genuine scalar profiles for the source [X,π] boundary. The three graph
templates have their proved signs +,−,+ and every incoming edge assignment. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace EnvelopingIsomorphism.Deformation.MixedGraphActionSplits
open scoped BigOperators Classical
open KontsevichGraph.General KontsevichGraph.General.TwoVertexContraction
open UniformBinaryGraphs SchoutenGraphContraction MixedGraphProfileCarrier GraphCoefficientProfiles

variable {n : ℕ}

theorem actionSplitArity (i : Fin (n + 1)) :
    vertexSplitArity (fun _ : Fin (n + 1) ↦ 2) vectorBivectorArity i =
      Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 (vertexSplitChild i 0) := by
  funext v
  obtain ⟨s, rfl⟩ := (vertexSplitSourceEquiv i).symm.surjective v
  cases s with
  | inl v =>
    rw [vertexSplitSourceEquiv_symm_old, vertexSplitArity_old _ _ _ _ v.property]
    exact (if_neg (vertexSplitOld_ne_child i v.val v.property 0)).symm
  | inr c =>
    simp only [vertexSplitSourceEquiv_symm_child, vertexSplitArity_child]
    fin_cases c
    · exact (if_pos rfl).symm
    · have hc : vertexSplitChild i 1 ≠ vertexSplitChild i 0 :=
        fun h ↦ (by decide : (1 : Fin 2) ≠ 0) (vertexSplitChild_injective i h)
      exact (if_neg hc).symm

abbrev SplitChoices (Θ : BinaryGraph (n + 1) 2) (i : Fin (n + 1)) := Θ.VertexSplitChoices i

def splitForward (Θ : BinaryGraph (n + 1) 2) (i : Fin (n + 1)) (χ : SplitChoices Θ i) :
    VectorGraph (n + 1) 2 :=
  ofProfile (vertexSplitChild i 0) (actionSplitArity i)
    (Θ.vertexSplit vectorBivectorForward i rfl χ)

def splitBackward (Θ : BinaryGraph (n + 1) 2) (i : Fin (n + 1))
    (ρ : Equiv.Perm (Fin 2)) (χ : SplitChoices Θ i) : VectorGraph (n + 1) 2 :=
  ofProfile (vertexSplitChild i 0) (actionSplitArity i)
    (Θ.vertexSplit (vectorBivectorBackward ρ) i rfl χ)

variable {k : Type*} [Field k] [CharZero k] {d : ℕ}

/-- Pure scalar source profile: the actual three-term signed split fibre sum. -/
def actionSplitProfile (Θ : BinaryGraph (n + 1) 2) (i : Fin (n + 1)) : VectorGraph (n + 1) 2 → k :=
  pushforward (splitForward Θ i) (fun _ ↦ 1) -
    pushforward (splitBackward Θ i 1) (fun _ ↦ 1) +
    pushforward (splitBackward Θ i (Equiv.swap 0 1)) (fun _ ↦ 1)

omit [CharZero k] in
theorem actionSplitProfile_apply (Θ : BinaryGraph (n + 1) 2) (i : Fin (n + 1))
    (H : VectorGraph (n + 1) 2) :
    actionSplitProfile (k := k) Θ i H = ∑ χ : SplitChoices Θ i,
      ((if splitForward Θ i χ = H then 1 else 0) -
        (if splitBackward Θ i 1 χ = H then 1 else 0) +
        (if splitBackward Θ i (Equiv.swap 0 1) χ = H then 1 else 0)) := by
  simp only [actionSplitProfile, Pi.add_apply, Pi.sub_apply, pushforward_apply,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  apply congrArg₂ (fun x y : k ↦ x + y)
  · apply congrArg₂ (fun x y : k ↦ x - y)
    · apply Finset.sum_congr rfl
      intro χ hχ
      split_ifs <;> rfl
    · apply Finset.sum_congr rfl
      intro χ hχ
      split_ifs <;> rfl
  · apply Finset.sum_congr rfl
    intro χ hχ
    split_ifs <;> rfl

/-- Every binary quotient vertex is available for the derivative's action insertion. -/
def sourceActionProfile (w : BinaryGraph (n + 1) 2 → k) : VectorGraph (n + 1) 2 → k :=
  ∑ Θ : BinaryGraph (n + 1) 2, ∑ i : Fin (n + 1), w Θ • actionSplitProfile Θ i

def outsideTensors (i : Fin (n + 1))
    (B : Fin (n + 2) → Bivector (k := k) (d := d)) (v : Fin (n + 1)) : Tensor 2 d k :=
  rawTensor (B (vertexSplitOldEmbedding i v))

omit [CharZero k] in
private theorem castTensors_heq {m : ℕ} {q q' : Fin m → ℕ} (h : q = q')
    (T : (v : Fin m) → Tensor (q v) d k) (v : Fin m) : HEq (castTensors h T v) (T v) := by
  cases h
  rfl

omit [CharZero k] in
/-- Tensor transport is checked separately at every surviving vertex and both
children. The vector and all bivectors are independent inputs. -/
theorem splitTensors_eq_raw (i : Fin (n + 1))
    (B : Fin (n + 2) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    castTensors (actionSplitArity i)
      (vertexSplitTensors (fun _ ↦ 2) vectorBivectorArity i (outsideTensors i B)
        (vectorBivectorPairTensors X (B (vertexSplitChild i 1)))) =
      rawTensors (vertexSplitChild i 0) B X := by
  funext v
  obtain ⟨s, rfl⟩ := (vertexSplitSourceEquiv i).symm.surjective v
  cases s with
  | inl v =>
    rw [vertexSplitSourceEquiv_symm_old]
    apply eq_of_heq
    exact ((castTensors_heq _ _ _).trans
      (vertexSplitTensors_old_heq _ _ _ _ _ v.val v.property)).trans
      (rawTensors_other_heq _ _ (vertexSplitOld_ne_child i v.val v.property 0) B X).symm
  | inr c =>
    rw [vertexSplitSourceEquiv_symm_child]
    apply eq_of_heq
    have he := (castTensors_heq (actionSplitArity i)
      (vertexSplitTensors (fun _ ↦ 2) vectorBivectorArity i (outsideTensors i B)
        (vectorBivectorPairTensors X (B (vertexSplitChild i 1)))) _).trans
      (vertexSplitTensors_child_heq _ _ _ _ _ c)
    fin_cases c
    · exact he.trans (rawTensors_root_heq _ B X).symm
    · have hc : vertexSplitChild i 1 ≠ vertexSplitChild i 0 :=
        fun h ↦ (by decide : (1 : Fin 2) ≠ 0) (vertexSplitChild_injective i h)
      exact he.trans (rawTensors_other_heq _ _ hc B X).symm

omit [CharZero k] in
private theorem rawValue_forward (Θ : BinaryGraph (n + 1) 2) (i : Fin (n + 1))
    (χ : SplitChoices Θ i) (B : Fin (n + 2) → Bivector (k := k) (d := d))
    (X : Vector (k := k) (d := d)) :
    rawValue (splitForward Θ i χ) B X =
      (Θ.vertexSplit vectorBivectorForward i rfl χ).cochainOperator
        (vertexSplitTensors (fun _ ↦ 2) vectorBivectorArity i (outsideTensors i B)
          (vectorBivectorPairTensors X (B (vertexSplitChild i 1)))) := by
  change (castGraph (actionSplitArity i) _).cochainOperator (rawTensors _ B X) = _
  rw [← splitTensors_eq_raw]
  exact cochainOperator_castGraph _ _ _

omit [CharZero k] in
private theorem rawValue_backward (Θ : BinaryGraph (n + 1) 2) (i : Fin (n + 1))
    (ρ : Equiv.Perm (Fin 2)) (χ : SplitChoices Θ i)
    (B : Fin (n + 2) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    rawValue (splitBackward Θ i ρ χ) B X =
      (Θ.vertexSplit (vectorBivectorBackward ρ) i rfl χ).cochainOperator
        (vertexSplitTensors (fun _ ↦ 2) vectorBivectorArity i (outsideTensors i B)
          (vectorBivectorPairTensors X (B (vertexSplitChild i 1)))) := by
  change (castGraph (actionSplitArity i) _).cochainOperator (rawTensors _ B X) = _
  rw [← splitTensors_eq_raw]
  exact cochainOperator_castGraph _ _ _

/-- Exact raw scalar-profile evaluation at arbitrary tensors, before using
the increasing complement ordering of the common mixed carrier. -/
theorem evaluation_actionSplitProfile_raw (Θ : BinaryGraph (n + 1) 2) (i : Fin (n + 1))
    (B : Fin (n + 2) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    evaluation (fun H ↦ rawValue H B X) (actionSplitProfile (k := k) Θ i) =
      Θ.cochainOperator (Function.update (outsideTensors i B) i
        (rawTensor (schoutenVectorAction 1 X (B (vertexSplitChild i 1))))) := by
  simp only [actionSplitProfile, map_add, map_sub, evaluation_pushforward, one_smul]
  apply MultilinearMap.ext
  intro f
  have h := cochainOperator_vector_bivector_vertexSplit Θ i rfl (outsideTensors i B)
    X (B (vertexSplitChild i 1)) f
  simpa only [tensorCast_rfl, sum_apply, sub_apply, add_apply,
    rawValue_forward, rawValue_backward] using h.symm

/-- Inserting the vector child immediately before its original bivector
preserves the increasing order of all n+1 bivector slots. -/
theorem placementEquiv_split_old (i j : Fin (n + 1)) :
    placementEquiv (vertexSplitChild i 0) (Sum.inl j) = vertexSplitOldEmbedding i j := by
  change ({vertexSplitChild i 0}ᶜ : Finset (Fin (n + 2))).orderEmbOfFin
    (Gauge.PlacedMixedGraphTaylorCoefficients.card_bivectorSlots (vertexSplitChild i 0)) j = _
  exact Finset.orderEmbOfFin_compl_singleton_apply _ j

def expandedBackground (i : Fin (n + 1))
    (R : Fin (n + 1) → Bivector (k := k) (d := d)) : Fin (n + 2) → Bivector (k := k) (d := d) :=
  fun v ↦ R (vertexSplitCollapse i v)

omit [CharZero k] in
theorem expandedBackground_old (i j : Fin (n + 1))
    (R : Fin (n + 1) → Bivector (k := k) (d := d)) :
    expandedBackground i R (vertexSplitOldEmbedding i j) = R j := by
  simp [expandedBackground, vertexSplitCollapse, vertexSplitOldEmbedding]

omit [CharZero k] in
theorem expandedBackground_child (i : Fin (n + 1)) (c : Fin 2)
    (R : Fin (n + 1) → Bivector (k := k) (d := d)) :
    expandedBackground i R (vertexSplitChild i c) = R i := by
  simp [expandedBackground, vertexSplitCollapse, vertexSplitChild]

omit [CharZero k] in
theorem operator_eq_expanded_raw (Γ : VectorGraph (n + 1) 2) (i : Fin (n + 1))
    (hi : Γ.vertex = vertexSplitChild i 0)
    (R : Fin (n + 1) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    MixedGraphProfileCarrier.operator Γ R X = rawValue Γ (expandedBackground i R) X := by
  have h := operator_eq_rawValue Γ (expandedBackground i R) X
  have he : (fun j ↦ expandedBackground i R (placementEquiv Γ.vertex (Sum.inl j))) = R := by
    funext j
    rw [hi, placementEquiv_split_old, expandedBackground_old]
  rw [he] at h
  exact h

/-- Source action split scalar coefficients evaluate to the actual derivative
insertion [X,R_i], while every other bivector input remains independently R_j. -/
theorem evaluation_actionSplitProfile_ordered (Θ : BinaryGraph (n + 1) 2) (i : Fin (n + 1))
    (R : Fin (n + 1) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    evaluation (fun H ↦ MixedGraphProfileCarrier.operator H R X) (actionSplitProfile (k := k) Θ i) =
      UniformBinaryGraphs.operator Θ (Function.update R i (schoutenVectorAction 1 X (R i))) := by
  have heval : evaluation (fun H ↦ MixedGraphProfileCarrier.operator H R X) (actionSplitProfile (k := k) Θ i) =
      evaluation (fun H ↦ rawValue H (expandedBackground i R) X) (actionSplitProfile (k := k) Θ i) := by
    simp only [actionSplitProfile, map_add, map_sub, evaluation_pushforward, one_smul]
    have hf (χ : SplitChoices Θ i) := operator_eq_expanded_raw (splitForward Θ i χ) i rfl R X
    have hb (ρ : Equiv.Perm (Fin 2)) (χ : SplitChoices Θ i) :=
      operator_eq_expanded_raw (splitBackward Θ i ρ χ) i rfl R X
    simp only [hf, hb]
  rw [heval, evaluation_actionSplitProfile_raw, expandedBackground_child, UniformBinaryGraphs.operator_apply]
  apply congrArg Θ.cochainOperator
  funext v
  by_cases hv : v = i
  · subst v
    simp only [Function.update_self]
    rfl
  · simp only [Function.update_of_ne hv, outsideTensors, expandedBackground_old]
    rfl

end EnvelopingIsomorphism.Deformation.MixedGraphActionSplits
