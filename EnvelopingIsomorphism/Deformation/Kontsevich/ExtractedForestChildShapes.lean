import EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedForestExtraction
import EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestShapeLimits

/-! Actual child increments obtained from the equal-value partitions of the extracted shapes. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestChildShapes

open SubsetNormalizedLimits ReflectedForestExtraction ComplexConjugate
open scoped Classical

variable {I : Type*} [Fintype I] [DecidableEq I]

section Parts

variable (q : ShapeFamily I) (A : LargeSubset I)

/-- Choose one actual label in each nonempty native partition part. -/
def representative (B : (partition q A.val).parts) : B.val :=
  ⟨((partition q A.val).nonempty_of_mem_parts B.property).choose,
    ((partition q A.val).nonempty_of_mem_parts B.property).choose_spec⟩

/-- The child shape is the extracted parent shape at that actual representative. -/
def partValue (B : (partition q A.val).parts) : ℂ :=
  q A ⟨(representative q A B).val,
    (partition q A.val).le B.property (representative q A B).property⟩

/-- The chosen representative disappears from the resulting value. -/
theorem partValue_eq_of_mem (B : (partition q A.val).parts) (j : I) (hj : j ∈ B.val) :
    partValue q A B = extendedShape q A j := by
  have hjA : j ∈ A.val := (partition q A.val).le B.property hj
  rw [extendedShape, dif_pos hjA]
  exact eq_shape_of_mem_same_part q A B.property _ _ (representative q A B).property hj

/-- Distinct children are distinct actual equal-value fibers, so their shape values are distinct. -/
theorem partValue_injective : Function.Injective (partValue q A) := by
  intro B C h
  let j := representative q A B
  let k := representative q A C
  have hjA : j.val ∈ A.val := (partition q A.val).le B.property j.property
  have hkA : k.val ∈ A.val := (partition q A.val).le C.property k.property
  have hjk : extendedShape q A j.val = extendedShape q A k.val := by
    rw [← partValue_eq_of_mem q A B j.val j.property, ← partValue_eq_of_mem q A C k.val k.property]
    exact h
  have hkpart : k.val ∈ (partition q A.val).part j.val := by
    simp only [SubsetNormalizedLimits.partition, dif_pos A.property]
    exact (Finpartition.mem_part_ofSetSetoid_iff_rel A.val).mpr ⟨hjA, hkA, hjk⟩
  rw [(partition q A.val).part_eq_of_mem B.property j.property] at hkpart
  apply Subtype.ext
  exact (partition q A.val).eq_of_mem_parts B.property C.property hkpart k.property

end Parts

section Tree

variable {σ : I → I} {hσ : Function.Involutive σ} {p : ℕ → I → ℂ}
variable (E : Extraction σ hσ p) (R : Finset I) (hR : R.Nonempty)

private theorem label_ne_root (v : E.tree R hR) (hv : v ≠ ⊥) : v.val ≠ R := by
  intro h
  apply hv
  apply ClusterPartitionTree.tree_label_injective
  exact h

private theorem parentPart (v : E.tree R hR) (hv : v ≠ ⊥) :
    1 < (Order.pred v).val.card ∧ v.val ∈ (E.partitions (Order.pred v).val).parts :=
  ClusterPartitionTree.parent_part v (label_ne_root E R hR v hv)

def parentSubset (v : E.tree R hR) (hv : v ≠ ⊥) : LargeSubset I :=
  ⟨(Order.pred v).val, (parentPart E R hR v hv).1⟩

def nativeChildPart (v : E.tree R hR) (hv : v ≠ ⊥) :
    (partition E.shapes (parentSubset E R hR v hv).val).parts :=
  ⟨v.val, (parentPart E R hR v hv).2⟩

/-- Root increment is zero; every other increment is its actual parent's child-fiber value. -/
def increment (v : E.tree R hR) : ℂ :=
  if hv : v = ⊥ then 0 else
    partValue E.shapes (parentSubset E R hR v hv) (nativeChildPart E R hR v hv)

@[simp] theorem increment_root : increment E R hR ⊥ = 0 := by simp [increment]

theorem increment_eq_partValue_of_child (c d : E.tree R hR) (hcd : c ⋖ d) :
    increment E R hR d = partValue E.shapes
      ⟨c.val, ((E.tree_child_iff_partition R hR c d).mp hcd).1⟩
      ⟨d.val, ((E.tree_child_iff_partition R hR c d).mp hcd).2⟩ := by
  have hd : d ≠ ⊥ := ne_of_gt (lt_of_le_of_lt bot_le hcd.lt)
  rw [increment, dif_neg hd]
  have hp := hcd.pred_eq
  subst c
  rfl

/-- Any member of a child, not only the chosen one, gives the literal increment. -/
theorem increment_eq_shape_of_child (c d : E.tree R hR) (hcd : c ⋖ d) (j : I) (hj : j ∈ d.val) :
    increment E R hR d = extendedShape E.shapes
      ⟨c.val, ((E.tree_child_iff_partition R hR c d).mp hcd).1⟩ j := by
  rw [increment_eq_partValue_of_child E R hR c d hcd]
  exact partValue_eq_of_mem _ _ _ j hj

theorem siblings_distinct (c d e : E.tree R hR) (hcd : c ⋖ d) (hce : c ⋖ e) (hne : d ≠ e) :
    increment E R hR d ≠ increment E R hR e := by
  intro h
  rw [increment_eq_partValue_of_child E R hR c d hcd,
    increment_eq_partValue_of_child E R hR c e hce] at h
  have he := partValue_injective E.shapes ⟨c.val, ((E.tree_child_iff_partition R hR c d).mp hcd).1⟩ h
  apply hne
  apply Subtype.ext
  exact congrArg (fun B : (partition E.shapes c.val).parts => B.val) he

theorem increment_reflect (hroot : R.image σ = R) (v : E.tree R hR) :
    increment E R hR (E.reflection R hR hroot v) = conj (increment E R hR v) := by
  by_cases hv : v = ⊥
  · subst v
    rw [(E.reflection R hR hroot).map_bot, increment_root, map_zero]
  · let c := Order.pred v
    have hcv : c ⋖ v := (E.tree_child_iff_partition R hR c v).mpr (parentPart E R hR v hv)
    have hrcv : E.reflection R hR hroot c ⋖ E.reflection R hR hroot v :=
      (ReflectedPartitionTree.reflect_cover_iff σ hσ E.partitions E.partitions_mirror
        E.partitions_proper R hR hroot c v).mpr hcv
    obtain ⟨j, hj⟩ := ClusterPartitionTree.nonempty_of_mem_clusters E.partitions E.partitions_proper
      R v.val hR v.property
    have hrj : σ j ∈ (E.reflection R hR hroot v).val := by
      rw [Extraction.reflection_label]
      exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
    let A : LargeSubset I := ⟨c.val, ((E.tree_child_iff_partition R hR c v).mp hcv).1⟩
    let B : LargeSubset I := ⟨(E.reflection R hR hroot c).val,
      ((E.tree_child_iff_partition R hR _ _).mp hrcv).1⟩
    have hAB : ReflectedSubsetNormalization.reflectLargeSubset σ hσ A = B := by
      apply Subtype.ext
      exact ReflectedSubsetPartitions.reflectLargeSubset_val_eq_image σ hσ A
    have hleft := increment_eq_shape_of_child E R hR _ _ hrcv (σ j) hrj
    have hright := increment_eq_shape_of_child E R hR c v hcv j hj
    change increment E R hR (E.reflection R hR hroot v) = extendedShape E.shapes B (σ j) at hleft
    change increment E R hR v = extendedShape E.shapes A j at hright
    rw [hleft, ← hAB, ReflectedSubsetPartitions.extendedShape_mirror σ hσ E.shapes E.shapes_mirror, ← hright]

theorem increment_sub_eq_shapes (c d e : E.tree R hR) (hcd : c ⋖ d) (hce : c ⋖ e)
    (j k : I) (hj : j ∈ d.val) (hk : k ∈ e.val) :
    increment E R hR d - increment E R hR e =
      E.shapes ⟨c.val, ((E.tree_child_iff_partition R hR c d).mp hcd).1⟩
        ⟨j, (E.partitions c.val).le ((E.tree_child_iff_partition R hR c d).mp hcd).2 hj⟩ -
      E.shapes ⟨c.val, ((E.tree_child_iff_partition R hR c d).mp hcd).1⟩
        ⟨k, (E.partitions c.val).le ((E.tree_child_iff_partition R hR c e).mp hce).2 hk⟩ := by
  rw [increment_eq_shape_of_child E R hR c d hcd j hj,
    increment_eq_shape_of_child E R hR c e hce k hk]
  simp only [extendedShape, dif_pos ((E.partitions c.val).le ((E.tree_child_iff_partition R hR c d).mp hcd).2 hj),
    dif_pos ((E.partitions c.val).le ((E.tree_child_iff_partition R hR c e).mp hce).2 hk)]

/-- Strict upper/lower separation follows from the original weak imaginary sign,
zero real difference, and the actually distinct native child fibers. -/
theorem increment_sub_im_pos_of_original (c d e : E.tree R hR) (hcd : c ⋖ d) (hce : c ⋖ e) (hne : d ≠ e)
    (j k : I) (hj : j ∈ d.val) (hk : k ∈ e.val)
    (hre : ∀ n, (p n j - p n k).re = 0) (him : ∀ n, 0 ≤ (p n j - p n k).im) :
    0 < (increment E R hR d - increment E R hR e).im := by
  let A : LargeSubset I := ⟨c.val, ((E.tree_child_iff_partition R hR c d).mp hcd).1⟩
  let jA : A.val := ⟨j, (E.partitions c.val).le ((E.tree_child_iff_partition R hR c d).mp hcd).2 hj⟩
  let kA : A.val := ⟨k, (E.partitions c.val).le ((E.tree_child_iff_partition R hR c e).mp hce).2 hk⟩
  have hq : increment E R hR d - increment E R hR e = E.shapes A jA - E.shapes A kA :=
    increment_sub_eq_shapes E R hR c d e hcd hce j k hj hk
  have hR0 : (increment E R hR d - increment E R hR e).re = 0 := by
    rw [hq]
    exact ExtractedForestShapeLimits.shape_sub_re_eq_zero E A jA kA hre
  have hI0 : 0 ≤ (increment E R hR d - increment E R hR e).im := by
    rw [hq]
    exact ExtractedForestShapeLimits.shape_sub_im_nonneg E A jA kA him
  have hne0 : increment E R hR d - increment E R hR e ≠ 0 :=
    sub_ne_zero.mpr (siblings_distinct E R hR c d e hcd hce hne)
  have himne : (increment E R hR d - increment E R hR e).im ≠ 0 := by
    intro h
    exact hne0 (Complex.ext hR0 h)
  exact lt_of_le_of_ne hI0 himne.symm

/-- Strict boundary order follows from the original weak real sign and actual fiber separation. -/
theorem increment_sub_re_pos_of_original (c d e : E.tree R hR) (hcd : c ⋖ d) (hce : c ⋖ e) (hne : d ≠ e)
    (j k : I) (hj : j ∈ d.val) (hk : k ∈ e.val)
    (him : ∀ n, (p n j - p n k).im = 0) (hre : ∀ n, 0 ≤ (p n j - p n k).re) :
    0 < (increment E R hR d - increment E R hR e).re := by
  let A : LargeSubset I := ⟨c.val, ((E.tree_child_iff_partition R hR c d).mp hcd).1⟩
  let jA : A.val := ⟨j, (E.partitions c.val).le ((E.tree_child_iff_partition R hR c d).mp hcd).2 hj⟩
  let kA : A.val := ⟨k, (E.partitions c.val).le ((E.tree_child_iff_partition R hR c e).mp hce).2 hk⟩
  have hq : increment E R hR d - increment E R hR e = E.shapes A jA - E.shapes A kA :=
    increment_sub_eq_shapes E R hR c d e hcd hce j k hj hk
  have hI0 : (increment E R hR d - increment E R hR e).im = 0 := by
    rw [hq]
    exact ExtractedForestShapeLimits.shape_sub_im_eq_zero E A jA kA him
  have hR0 : 0 ≤ (increment E R hR d - increment E R hR e).re := by
    rw [hq]
    exact ExtractedForestShapeLimits.shape_sub_re_nonneg E A jA kA hre
  have hne0 : increment E R hR d - increment E R hR e ≠ 0 :=
    sub_ne_zero.mpr (siblings_distinct E R hR c d e hcd hce hne)
  have hrene : (increment E R hR d - increment E R hR e).re ≠ 0 := by
    intro h
    exact hne0 (Complex.ext h hI0)
  exact lt_of_le_of_ne hR0 hrene.symm

end Tree

end EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestChildShapes
