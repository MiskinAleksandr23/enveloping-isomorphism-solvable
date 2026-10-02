import EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestIdentification
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestMarkedFrames

/-! Genuine marked-frame choices on every actual extracted forest. Nonstable
nodes choose two children equivariantly; stable nodes use an upper child when
one exists, and otherwise use two ordered real fixed children. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestFrames

open Configuration ComplexConjugate ForestMarkedFrames
open ExtractedForestParameters ExtractedForestChildShapes ReflectedForestExtraction
open scoped Classical

variable {n m : ℕ} (i : Fin n) (x : Compactification i m)

abbrev reflection : tree i x ≃o tree i x := compactificationReflection i x

@[simp] theorem reflection_reflection (v : tree i x) : reflection i x (reflection i x v) = v :=
  (shapeData i x).reflection_involutive v

theorem reflection_nonleaf (v : tree i x) (hv : ¬IsMax v) : ¬IsMax (reflection i x v) :=
  fun h => hv ((reflection i x).isMax_apply.mp h)

theorem reflection_child {v w : tree i x} (h : v ⋖ w) : reflection i x v ⋖ reflection i x w :=
  (apply_covBy_apply_iff (reflection i x)).mpr h

theorem exists_child_pair (v : tree i x) (hv : ¬IsMax v) :
    ∃ a b : tree i x, v ⋖ a ∧ v ⋖ b ∧ a ≠ b := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp
    (ClusterPartitionTree.one_lt_card_childNodes (hR := ⟨Sum.inr i, Finset.mem_univ _⟩) v hv)
  exact ⟨a, b, (ClusterPartitionTree.mem_childNodes (hR := ⟨Sum.inr i, Finset.mem_univ _⟩) v a).mp ha,
    (ClusterPartitionTree.mem_childNodes (hR := ⟨Sum.inr i, Finset.mem_univ _⟩) v b).mp hb, hab⟩

def chosenPair (v : tree i x) (hv : ¬IsMax v) : tree i x × tree i x :=
  ((exists_child_pair i x v hv).choose, (exists_child_pair i x v hv).choose_spec.choose)

theorem chosenPair_spec (v : tree i x) (hv : ¬IsMax v) :
    v ⋖ (chosenPair i x v hv).1 ∧ v ⋖ (chosenPair i x v hv).2 ∧
      (chosenPair i x v hv).1 ≠ (chosenPair i x v hv).2 :=
  (exists_child_pair i x v hv).choose_spec.choose_spec

def nodeCode (v : tree i x) : ℕ := (Fintype.equivFin (tree i x) v).val

theorem nodeCode_injective : Function.Injective (nodeCode i x) :=
  fun _ _ h => (Fintype.equivFin (tree i x)).injective (Fin.ext h)

/-- Choose arbitrarily only on one side of each reflection orbit. -/
def markedPair (v : tree i x) (hv : ¬IsMax v) : tree i x × tree i x :=
  if nodeCode i x v ≤ nodeCode i x (reflection i x v) then chosenPair i x v hv else
    let q := chosenPair i x (reflection i x v) (reflection_nonleaf i x v hv)
    (reflection i x q.1, reflection i x q.2)

theorem markedPair_spec (v : tree i x) (hv : ¬IsMax v) :
    v ⋖ (markedPair i x v hv).1 ∧ v ⋖ (markedPair i x v hv).2 ∧
      (markedPair i x v hv).1 ≠ (markedPair i x v hv).2 := by
  unfold markedPair
  split_ifs
  · exact chosenPair_spec i x v hv
  · have h := chosenPair_spec i x (reflection i x v) (reflection_nonleaf i x v hv)
    exact ⟨by simpa using reflection_child i x h.1,
      by simpa using reflection_child i x h.2.1, (reflection i x).injective.ne h.2.2⟩

/-- Both ordered marks commute with reflection on every nonstable node orbit. -/
theorem markedPair_reflection (v : tree i x) (hv : ¬IsMax v) (hs : reflection i x v ≠ v) :
    markedPair i x (reflection i x v) (reflection_nonleaf i x v hv) =
      (reflection i x (markedPair i x v hv).1, reflection i x (markedPair i x v hv).2) := by
  have hc : nodeCode i x (reflection i x v) ≠ nodeCode i x v :=
    (nodeCode_injective i x).ne hs
  unfold markedPair
  simp only [reflection_reflection]
  by_cases h : nodeCode i x v ≤ nodeCode i x (reflection i x v)
  · have hh : ¬nodeCode i x (reflection i x v) ≤ nodeCode i x v := by omega
    simp only [if_pos h, if_neg hh]
  · have hh : nodeCode i x (reflection i x v) ≤ nodeCode i x v := by omega
    simp only [if_neg h, if_pos hh, reflection_reflection]

def HasUpperChild (v : tree i x) : Prop :=
  ∃ a : tree i x, v ⋖ a ∧ 0 < (canonicalIncrement i x a).im

/-- In a stable node without upper children every child is genuinely real. -/
theorem child_real_of_no_upper (v : tree i x) (hs : reflection i x v = v)
    (hu : ¬HasUpperChild i x v) (a : tree i x) (ha : v ⋖ a) :
    (canonicalIncrement i x a).im = 0 := by
  have hn : ¬0 < (canonicalIncrement i x a).im := fun h => hu ⟨a, ha, h⟩
  have hna : ¬(canonicalIncrement i x a).im < 0 := by
    intro h
    apply hu
    refine ⟨reflection i x a, ?_, ?_⟩
    · simpa only [hs] using reflection_child i x ha
    · rw [canonicalIncrement_reflect, Complex.conj_im]
      exact neg_pos.mpr h
  exact le_antisymm (le_of_not_gt hn) (le_of_not_gt hna)

/-- Such real children are fixed nodes, by injectivity of the actual sibling shapes. -/
theorem child_fixed_of_no_upper (v : tree i x) (hs : reflection i x v = v)
    (hu : ¬HasUpperChild i x v) (a : tree i x) (ha : v ⋖ a) : reflection i x a = a := by
  by_contra hne
  have hra : v ⋖ reflection i x a := by simpa only [hs] using reflection_child i x ha
  apply canonicalIncrement_siblings_distinct i x v _ a hra ha hne
  rw [canonicalIncrement_reflect]
  exact Complex.conj_eq_iff_im.mpr (child_real_of_no_upper i x v hs hu a ha)

theorem exists_ordered_real_pair (v : tree i x) (hv : ¬IsMax v)
    (hs : reflection i x v = v) (hu : ¬HasUpperChild i x v) :
    ∃ a b : tree i x, v ⋖ a ∧ v ⋖ b ∧ a ≠ b ∧
      (canonicalIncrement i x a).re < (canonicalIncrement i x b).re := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_child_pair i x v hv
  have hne : (canonicalIncrement i x a).re ≠ (canonicalIncrement i x b).re := by
    intro he
    exact canonicalIncrement_siblings_distinct i x v a b ha hb hab
      (Complex.ext he ((child_real_of_no_upper i x v hs hu a ha).trans
        (child_real_of_no_upper i x v hs hu b hb).symm))
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨a, b, ha, hb, hab, h⟩
  · exact ⟨b, a, hb, ha, hab.symm, h⟩

def realPair (v : tree i x) (hv : ¬IsMax v) (hs : reflection i x v = v)
    (hu : ¬HasUpperChild i x v) : tree i x × tree i x :=
  ((exists_ordered_real_pair i x v hv hs hu).choose,
    (exists_ordered_real_pair i x v hv hs hu).choose_spec.choose)

theorem realPair_spec (v : tree i x) (hv : ¬IsMax v) (hs : reflection i x v = v)
    (hu : ¬HasUpperChild i x v) :
    v ⋖ (realPair i x v hv hs hu).1 ∧ v ⋖ (realPair i x v hv hs hu).2 ∧
      (realPair i x v hv hs hu).1 ≠ (realPair i x v hv hs hu).2 ∧
      (canonicalIncrement i x (realPair i x v hv hs hu).1).re <
        (canonicalIncrement i x (realPair i x v hv hs hu).2).re :=
  (exists_ordered_real_pair i x v hv hs hu).choose_spec.choose_spec

/-- Every nonleaf of the actual extracted tree receives an actual immediate-child frame. -/
def frames : Frames (tree i x) := fun v hv =>
  if hs : reflection i x v = v then
    if hu : HasUpperChild i x v then
      .stableHeight hu.choose hu.choose_spec.1
    else
      .stableRealPair (realPair i x v hv hs hu).1 (realPair i x v hv hs hu).2
        (realPair_spec i x v hv hs hu).1 (realPair_spec i x v hv hs hu).2.1
        (realPair_spec i x v hv hs hu).2.2.1
  else
    .complex (markedPair i x v hv).1 (markedPair i x v hv).2
      (markedPair_spec i x v hv).1 (markedPair_spec i x v hv).2.1 (markedPair_spec i x v hv).2.2

theorem frames_nonstable (v : tree i x) (hv : ¬IsMax v) (hs : reflection i x v ≠ v) :
    frames i x v hv = .complex (markedPair i x v hv).1 (markedPair i x v hv).2
      (markedPair_spec i x v hv).1 (markedPair_spec i x v hv).2.1 (markedPair_spec i x v hv).2.2 := by
  simp only [frames, dif_neg hs]

/-- The actual selected complex frame on the paired node uses precisely the
reflections of both original ordered child marks. -/
theorem frames_nonstable_reflection (v : tree i x) (hv : ¬IsMax v) (hs : reflection i x v ≠ v) :
    frames i x (reflection i x v) (reflection_nonleaf i x v hv) =
      .complex (reflection i x (markedPair i x v hv).1) (reflection i x (markedPair i x v hv).2)
        (reflection_child i x (markedPair_spec i x v hv).1)
        (reflection_child i x (markedPair_spec i x v hv).2.1)
        ((reflection i x).injective.ne (markedPair_spec i x v hv).2.2) := by
  have hs' : reflection i x (reflection i x v) ≠ reflection i x v := by
    simpa only [reflection_reflection] using hs.symm
  rw [frames_nonstable i x _ _ hs']
  simp only [markedPair_reflection i x v hv hs]

/-- Node type and fixed real marks are consequences of the selected frame. -/
def TypeCorrect (v : tree i x) (f : Frame (tree i x) v) : Prop :=
  match f with
  | .complex _ _ _ _ _ => reflection i x v ≠ v
  | .stableHeight a _ => reflection i x v = v ∧ 0 < (canonicalIncrement i x a).im
  | .stableRealPair a b _ _ _ => reflection i x v = v ∧
      reflection i x a = a ∧ reflection i x b = b ∧
      (canonicalIncrement i x a).im = 0 ∧ (canonicalIncrement i x b).im = 0

theorem frames_typeCorrect (v : tree i x) (hv : ¬IsMax v) :
    TypeCorrect i x v (frames i x v hv) := by
  unfold frames
  split_ifs with hs hu
  · exact ⟨hs, hu.choose_spec.2⟩
  · exact ⟨hs,
      child_fixed_of_no_upper i x v hs hu _ (realPair_spec i x v hv hs hu).1,
      child_fixed_of_no_upper i x v hs hu _ (realPair_spec i x v hv hs hu).2.1,
      child_real_of_no_upper i x v hs hu _ (realPair_spec i x v hv hs hu).1,
      child_real_of_no_upper i x v hs hu _ (realPair_spec i x v hv hs hu).2.1⟩
  · exact hs

/-- Every chosen frame has a strictly positive leading radius on the actual
extracted child array; no frame-existence or positivity premise is supplied. -/
theorem leadingRadius_pos (v : tree i x) (hv : ¬IsMax v) :
    0 < (frames i x v hv).radius (canonicalIncrement i x) := by
  unfold frames
  split_ifs with hs hu
  · exact hu.choose_spec.2
  · exact sub_pos.mpr (realPair_spec i x v hv hs hu).2.2.2
  · apply norm_pos_iff.mpr
    exact sub_ne_zero.mpr (canonicalIncrement_siblings_distinct i x v _ _
      (markedPair_spec i x v hv).2.1 (markedPair_spec i x v hv).1
      (markedPair_spec i x v hv).2.2.symm)

/-- The real-pair case supplies the actual real child values needed by the
factory's exact zero/one normalization theorems. -/
theorem realPair_children_real (v : tree i x) (hv : ¬IsMax v) (hs : reflection i x v = v)
    (hu : ¬HasUpperChild i x v) :
    (canonicalIncrement i x (realPair i x v hv hs hu).1).im = 0 ∧
      (canonicalIncrement i x (realPair i x v hv hs hu).2).im = 0 :=
  ⟨child_real_of_no_upper i x v hs hu _ (realPair_spec i x v hv hs hu).1,
    child_real_of_no_upper i x v hs hu _ (realPair_spec i x v hv hs hu).2.1⟩

theorem realPair_children_fixed (v : tree i x) (hv : ¬IsMax v) (hs : reflection i x v = v)
    (hu : ¬HasUpperChild i x v) :
    reflection i x (realPair i x v hv hs hu).1 = (realPair i x v hv hs hu).1 ∧
      reflection i x (realPair i x v hv hs hu).2 = (realPair i x v hv hs hu).2 :=
  ⟨child_fixed_of_no_upper i x v hs hu _ (realPair_spec i x v hv hs hu).1,
    child_fixed_of_no_upper i x v hs hu _ (realPair_spec i x v hv hs hu).2.1⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestFrames
