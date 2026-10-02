import EnvelopingIsomorphism.Deformation.Kontsevich.ForestGlobalGraphStokes

/-! Actual radial Stokes faces indexed by reflection orbits of nonroot
internal nodes. Higher-codimension intersections have zero native face measure.
The label partition is independent of any simple-cluster chart identification. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestRadialFaceClassification

open Set MeasureTheory BoxStokes CompactOrthantStokes OrthantInteriorIntegration
open ExtractedForestParameters ExtractedForestFrames ReflectedRadiusCoordinates
open ExtractedForestChildShapes Configuration
open scoped Classical NNReal

inductive Kind
  | paired
  | pureBoundary
  | properReal
  | infinity
  deriving DecidableEq, Fintype

variable {n m : ℕ} (i : Fin n) (x : Compactification i m)

abbrev Orbit := ReflectedRadiusCoordinates.Orbit (tree i x) (reflection i x)
  (reflection_reflection i x)

def nodeKind (v : tree i x) : Kind :=
  if reflection i x v = v then
    if ∀ j : Fin n, Sum.inl (Sum.inl j) ∉ v.val then .pureBoundary
    else if ∀ j : Fin n, Sum.inl (Sum.inl j) ∈ v.val then .infinity
    else .properReal
  else .paired

@[simp] theorem nodeKind_reflection (v : tree i x) :
    nodeKind i x (reflection i x v) = nodeKind i x v := by
  by_cases hv : reflection i x v = v
  · rw [hv]
  · have hrv : reflection i x (reflection i x v) ≠ reflection i x v := by
      simpa only [reflection_reflection] using Ne.symm hv
    simp only [nodeKind, if_neg hv, if_neg hrv]

/-- The class is independent of the representative of the actual radial orbit. -/
def kind : Orbit i x → Kind :=
  Quotient.lift (fun v : ActiveNode (tree i x) => nodeKind i x v.val) (by
    intro u v huv
    rcases huv with rfl | huv
    · rfl
    · rw [← huv]
      exact (nodeKind_reflection i x u.val).symm)

@[simp] theorem kind_orbitClass (v : ActiveNode (tree i x)) :
    kind i x (orbitClass (tree i x) (reflection i x) (reflection_reflection i x) v) =
      nodeKind i x v.val := rfl

/-- Precisely the enumeration used by the actual free-radius chart. -/
def orbitEquiv : Orbit i x ≃ Fin (ForestOrthantCharts.R i x) :=
  Fintype.equivFin (ReflectedRadiusCoordinates.Orbit (tree i x) (reflection i x) (reflection_reflection i x))

def representative (o : Orbit i x) : ActiveNode (tree i x) := Quotient.out o

@[simp] theorem representative_orbit (o : Orbit i x) :
    orbitClass (tree i x) (reflection i x) (reflection_reflection i x)
      (representative i x o) = o := Quotient.out_eq o

theorem representative_nonroot (o : Orbit i x) : (representative i x o).val ≠ ⊥ :=
  (representative i x o).property.1

theorem representative_large (o : Orbit i x) : 1 < (representative i x o).val.val.card :=
  ExtractedForestIdentification.nonleaf_large i x _ (representative i x o).property.2

theorem kind_representative (o : Orbit i x) :
    nodeKind i x (representative i x o).val = kind i x o := by
  rw [← kind_orbitClass, representative_orbit]

/-- Each free coordinate is evaluation at its actual node radius. -/
theorem finCoordinates_orbitClass
    (p : ForestParameterProduct.RadiusSpace (tree i x) (reflection i x))
    (v : ActiveNode (tree i x)) :
    (ReflectedRadiusCoordinates.finCoordinatesHomeomorph (tree i x) (reflection i x)
      (reflection_reflection i x) p
      (orbitEquiv i x (orbitClass (tree i x) (reflection i x) (reflection_reflection i x) v)) : ℝ) =
      p.val v.val := by
  change ((Homeomorph.piCongrLeft
    (Y := fun _ : Fin (ForestOrthantCharts.R i x) => ℝ≥0)
    (orbitEquiv i x))
    (ReflectedRadiusCoordinates.coordinatesHomeomorph (tree i x) (reflection i x)
      (reflection_reflection i x) p)
    (orbitEquiv i x (orbitClass (tree i x) (reflection i x) (reflection_reflection i x) v)) : ℝ) = _
  rw [Homeomorph.piCongrLeft_apply_apply]
  rfl

theorem reflection_label (v : tree i x) :
    (reflection i x v).val = v.val.image Configuration.doubledReflection := rfl

theorem mem_reflection_iff (v : tree i x) (a : Configuration.DoubledLabel n m) :
    a ∈ (reflection i x v).val ↔ Configuration.doubledReflection a ∈ v.val := by
  rw [reflection_label]
  constructor
  · rintro h
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp h
    simpa only [Configuration.doubledReflection_involutive b] using hb
  · intro h
    exact Finset.mem_image.mpr ⟨Configuration.doubledReflection a, h,
      Configuration.doubledReflection_involutive a⟩

theorem fixed_mem_mirror_iff (v : tree i x) (hv : reflection i x v = v) (j : Fin n) :
    Sum.inr j ∈ v.val ↔ Sum.inl (Sum.inl j) ∈ v.val := by
  have h := mem_reflection_iff i x v (Sum.inr j)
  simpa only [hv, Configuration.doubledReflection] using h

theorem nodeKind_paired_iff (v : tree i x) :
    nodeKind i x v = .paired ↔ reflection i x v ≠ v := by
  unfold nodeKind
  split_ifs <;> simp_all

theorem nodeKind_pureBoundary_iff (v : tree i x) :
    nodeKind i x v = .pureBoundary ↔
      reflection i x v = v ∧ ∀ j : Fin n, Sum.inl (Sum.inl j) ∉ v.val := by
  unfold nodeKind
  split_ifs <;> simp_all

theorem nodeKind_properReal_iff (v : tree i x) :
    nodeKind i x v = .properReal ↔ reflection i x v = v ∧
      (∃ j : Fin n, Sum.inl (Sum.inl j) ∈ v.val) ∧
      (∃ j : Fin n, Sum.inl (Sum.inl j) ∉ v.val) := by
  unfold nodeKind
  split_ifs <;> simp_all

theorem nodeKind_infinity_iff (v : tree i x) :
    nodeKind i x v = .infinity ↔
      reflection i x v = v ∧ ∀ j : Fin n, Sum.inl (Sum.inl j) ∈ v.val := by
  have hn : Nonempty (Fin n) := ⟨i⟩
  unfold nodeKind
  split_ifs <;> simp_all

/-- Distinct reflection mates cannot be ancestors of each other. -/
theorem nonfixed_not_le (v : tree i x) (hv : reflection i x v ≠ v) :
    ¬v ≤ reflection i x v := by
  intro h
  have h' : reflection i x v ≤ v := by
    simpa only [reflection_reflection] using (reflection i x).monotone h
  exact hv (le_antisymm h' h)

private theorem inf_descendants {T : RootedTree} {v w a b : T}
    (hvw : ¬v ≤ w) (hwv : ¬w ≤ v) (hva : v ≤ a) (hwb : w ≤ b) :
    a ⊓ b = v ⊓ w := by
  apply le_antisymm
  · apply le_inf
    · rcases le_total_of_directed hva (inf_le_left : a ⊓ b ≤ a) with h | h
      · exact h
      · rcases le_total_of_directed hwb (h.trans inf_le_right) with hvw' | hwv'
        · exact (hvw hvw').elim
        · exact (hwv hwv').elim
    · rcases le_total_of_directed hwb (inf_le_right : a ⊓ b ≤ b) with h | h
      · exact h
      · rcases le_total_of_directed hva (h.trans inf_le_left) with hwv' | hvw'
        · exact (hwv hwv').elim
        · exact (hvw hvw').elim
  · exact inf_le_inf hva hwb

theorem nonfixed_no_boundary (v : tree i x) (hv : reflection i x v ≠ v) (j : Fin m) :
    Sum.inl (Sum.inr j) ∉ v.val := by
  intro hj
  have hrv : Sum.inl (Sum.inr j) ∈ (reflection i x v).val :=
    (mem_reflection_iff i x v _).mpr hj
  have hdis := (extraction i x).reflected_pair_disjoint Finset.univ
    ⟨Sum.inr i, Finset.mem_univ _⟩
    (ReflectedPartitionTree.image_univ doubledReflection doubledReflection_involutive) v hv
  exact Finset.disjoint_left.mp hdis hj hrv

/-- A paired extracted node cannot mix upper and lower labels. This uses the
actual upper-half-plane sign theorem, not only laminar combinatorics. -/
theorem nonfixed_no_mixed (v : tree i x) (hv : reflection i x v ≠ v)
    (j k : Fin n) (hj : Sum.inl (Sum.inl j) ∈ v.val) (hk : Sum.inr k ∈ v.val) : False := by
  have hvl : ¬ v ≤ reflection i x v := nonfixed_not_le i x v hv
  have hrv : ¬ reflection i x v ≤ v := by
    simpa only [reflection_reflection] using
      nonfixed_not_le i x (reflection i x v) (by simpa only [reflection_reflection] using Ne.symm hv)
  have hc : v ⊓ reflection i x v < v :=
    lt_iff_le_not_ge.mpr ⟨inf_le_left, fun h => hvl (h.trans inf_le_right)⟩
  obtain ⟨d, hd, hdv⟩ := ForestInsertionDifference.exists_child_between (tree i x) hc
  have he : (v ⊓ reflection i x v) ⋖ reflection i x d := by
    have h := (apply_covBy_apply_iff (reflection i x)).mpr hd
    simpa only [OrderIso.map_inf, reflection_reflection, inf_comm] using h
  have her : reflection i x d ≤ reflection i x v := (reflection i x).monotone hdv
  have hjv := (le_canonicalLeaf_iff i x v _).mpr hj
  have hkr := (le_canonicalLeaf_iff i x v _).mpr hk
  have hjr : reflection i x v ≤ canonicalLeaf i x (Sum.inr j) := by
    have h := (reflection i x).monotone hjv
    simpa only [reflection, canonicalLeaf_reflect, doubledReflection] using h
  have hkv : reflection i x v ≤ canonicalLeaf i x (Sum.inl (Sum.inl k)) := by
    have h := (reflection i x).monotone hkr
    simpa only [reflection, canonicalLeaf_reflect, doubledReflection] using h
  have hij := inf_descendants hvl hrv hjv hjr
  have hik := inf_descendants hrv hvl hkv hkr
  have hp := canonical_upper_gap i x j d (reflection i x d)
    (hij.symm ▸ hd) (hdv.trans hjv) (hij.symm ▸ he) (her.trans hjr)
  have hn := canonical_upper_gap i x k (reflection i x d) d
    (by simpa only [hik, inf_comm] using he) (her.trans hkv)
    (by simpa only [hik, inf_comm] using hd) (hdv.trans hkr)
  simp only [Complex.sub_im] at hp hn
  linarith

/-- Every nonfixed node is entirely on one genuine half-plane side. -/
theorem nonfixed_one_side (v : tree i x) (hv : reflection i x v ≠ v) :
    (∀ a ∈ v.val, ∃ j : Fin n, a = Sum.inl (Sum.inl j)) ∨
      (∀ a ∈ v.val, ∃ j : Fin n, a = Sum.inr j) := by
  by_cases hu : ∃ j : Fin n, Sum.inl (Sum.inl j) ∈ v.val
  · left
    obtain ⟨j, hj⟩ := hu
    intro a ha
    rcases a with (k | k) | k
    · exact ⟨k, rfl⟩
    · exact (nonfixed_no_boundary i x v hv k ha).elim
    · exact (nonfixed_no_mixed i x v hv j k hj ha).elim
  · right
    intro a ha
    rcases a with (k | k) | k
    · exact (hu ⟨k, ha⟩).elim
    · exact (nonfixed_no_boundary i x v hv k ha).elim
    · exact ⟨k, rfl⟩

section Stokes

variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n + 1)) m)

/-- The existing native axis belonging to one actual reflection orbit. -/
def axis (o : Orbit 0 x) : Fin (r + 1) :=
  ForestGlobalGraphStokes.radialIndex hdim x (orbitEquiv 0 x o)

theorem radialIndex_injective : Function.Injective (ForestGlobalGraphStokes.radialIndex hdim x) := by
  intro a b h
  apply Sum.inl_injective
  apply finSumFinEquiv.injective
  exact (finCongr _).injective h

theorem axis_injective : Function.Injective (axis hdim x) :=
  (radialIndex_injective hdim x).comp (orbitEquiv 0 x).injective

/-- The native face measure and original alternating outward sign are retained. -/
def contribution (θ : Form r) (o : Orbit 0 x) : ℝ :=
  -((-1 : ℝ) ^ (axis hdim x o).val) •
    ∫ z in orthant (faceIndices (ForestGlobalGraphStokes.radialIndices hdim x) (axis hdim x o)),
      facePullback θ (axis hdim x o) 0 z (standardBasis r)

/-- Literal reindexing, with no change of measure, bases, or orientation. -/
theorem lowerFaces_eq_sum_orbits (θ : Form r) :
    OrientedOrthantAssembly.lowerFaces θ (ForestGlobalGraphStokes.radialIndices hdim x) =
      ∑ o : Orbit 0 x, contribution hdim x θ o := by
  unfold OrientedOrthantAssembly.lowerFaces ForestGlobalGraphStokes.radialIndices
  rw [Finset.sum_image]
  · exact ((orbitEquiv 0 x).sum_comp (fun j =>
      -((-1 : ℝ) ^ (ForestGlobalGraphStokes.radialIndex hdim x j).val) •
        ∫ z in orthant (faceIndices
          (Finset.univ.image (ForestGlobalGraphStokes.radialIndex hdim x))
          (ForestGlobalGraphStokes.radialIndex hdim x j)),
          facePullback θ (ForestGlobalGraphStokes.radialIndex hdim x j) 0 z
            (standardBasis r))).symm
  · exact fun _ _ _ _ h => radialIndex_injective hdim x h

/-- The open part of a coordinate face has precisely one zero constrained
coordinate. -/
theorem strict_face_iff (S : Finset (Fin (r + 1))) (a : Fin (r + 1)) (z : Coord r) :
    z ∈ strictOrthant (faceIndices S a) ↔
      ∀ b ∈ S, b ≠ a → 0 < faceEmbedding a 0 z b := by
  constructor
  · intro hz b hb hba
    induction b using a.succAboveCases with
    | x => exact (hba rfl).elim
    | p b =>
      simpa only [faceEmbedding, Fin.insertNth_apply_succAbove] using
        hz b ((mem_faceIndices S a b).mpr hb)
  · intro hz b hb
    have h := hz (a.succAbove b) ((mem_faceIndices S a b).mp hb) (Fin.succAbove_ne a b)
    simpa only [faceEmbedding, Fin.insertNth_apply_succAbove] using h

/-- Actual ambient forest parameters on an orbit face. -/
def faceAmbient (o : Orbit 0 x) (z : Coord r) : ForestOrthantRealization.Ambient 0 x :=
  (ForestGlobalGraphStokes.sourceCoordinates hdim x).symm
    (faceEmbedding (axis hdim x o) 0 z)

theorem faceAmbient_radial (o o' : Orbit 0 x) (z : Coord r) :
    (faceAmbient hdim x o z).1 (orbitEquiv 0 x o') =
      faceEmbedding (axis hdim x o) 0 z (axis hdim x o') := by
  have h := ForestGlobalGraphStokes.sourceCoordinates_radial hdim x
    (faceAmbient hdim x o z) (orbitEquiv 0 x o')
  simpa only [faceAmbient, ContinuousLinearEquiv.apply_symm_apply, axis] using h.symm

@[simp] theorem faceAmbient_selected_zero (o : Orbit 0 x) (z : Coord r) :
    (faceAmbient hdim x o z).1 (orbitEquiv 0 x o) = 0 := by
  rw [faceAmbient_radial]
  simp [faceEmbedding]

theorem faceAmbient_other_positive (o o' : Orbit 0 x) (z : Coord r)
    (hz : z ∈ strictOrthant
      (faceIndices (ForestGlobalGraphStokes.radialIndices hdim x) (axis hdim x o)))
    (hne : o' ≠ o) : 0 < (faceAmbient hdim x o z).1 (orbitEquiv 0 x o') := by
  rw [faceAmbient_radial]
  apply (strict_face_iff _ _ z).mp hz
  · exact Finset.mem_image.mpr ⟨orbitEquiv 0 x o', Finset.mem_univ _, rfl⟩
  · exact fun h => hne (axis_injective hdim x h)

/-- The reconstructed native tree has exactly one zero reflection orbit. -/
theorem radiusArray_face_zero_iff (o : Orbit 0 x) (z : Coord r)
    (hz : z ∈ strictOrthant
      (faceIndices (ForestGlobalGraphStokes.radialIndices hdim x) (axis hdim x o)))
    (v : tree 0 x) :
    ForestOrthantRealization.radiusArray 0 x (faceAmbient hdim x o z) v = 0 ↔
      ∃ hv : Active (tree 0 x) v,
        orbitClass (tree 0 x) (reflection 0 x) (reflection_reflection 0 x) ⟨v, hv⟩ = o := by
  by_cases hv : Active (tree 0 x) v
  · rw [ForestOrthantRealization.radiusArray, dif_pos hv]
    change (faceAmbient hdim x o z).1
      (orbitEquiv 0 x (orbitClass (tree 0 x) (reflection 0 x) (reflection_reflection 0 x) ⟨v, hv⟩)) = 0 ↔ _
    constructor
    · intro h
      refine ⟨hv, ?_⟩
      by_contra hne
      exact (faceAmbient_other_positive hdim x o _ z hz hne).ne' h
    · rintro ⟨_, he⟩
      rw [he, faceAmbient_selected_zero]
  · simp only [ForestOrthantRealization.radiusArray, dif_neg hv, one_ne_zero, false_iff]
    exact fun ⟨hv', _⟩ => hv hv'

/-- Every strict descendant of a node in the selected orbit has genuinely
positive native radius, including the fixed unit radii of leaves. -/
theorem radiusArray_face_descendant_pos (o : Orbit 0 x) (z : Coord r)
    (hz : z ∈ strictOrthant
      (faceIndices (ForestGlobalGraphStokes.radialIndices hdim x) (axis hdim x o)))
    (c : ActiveNode (tree 0 x))
    (hc : orbitClass (tree 0 x) (reflection 0 x) (reflection_reflection 0 x) c = o)
    (v : tree 0 x) (hcv : c.val < v) :
    0 < ForestOrthantRealization.radiusArray 0 x (faceAmbient hdim x o z) v := by
  by_cases hv : Active (tree 0 x) v
  · rw [ForestOrthantRealization.radiusArray, dif_pos hv]
    change 0 < (faceAmbient hdim x o z).1
      (orbitEquiv 0 x (orbitClass (tree 0 x) (reflection 0 x) (reflection_reflection 0 x) ⟨v, hv⟩))
    apply faceAmbient_other_positive hdim x o _ z hz
    intro he
    have he' := (orbitClass_eq_iff (tree 0 x) (reflection 0 x) (reflection_reflection 0 x)
      c ⟨v, hv⟩).mp (hc.trans he.symm)
    rcases he' with he' | he'
    · exact hcv.ne (congrArg Subtype.val he')
    · have hev : reflection 0 x c.val = v := congrArg Subtype.val he'
      have hlt : c.val < reflection 0 x c.val := hev.symm ▸ hcv
      have hlt' : reflection 0 x c.val < c.val := by
        simpa only [reflection_reflection] using (reflection 0 x).strictMono hlt
      exact (lt_asymm hlt hlt')
  · simp only [ForestOrthantRealization.radiusArray, dif_neg hv, zero_lt_one]

/-- Other radial zero sets have zero native face measure. -/
theorem contribution_eq_strict (θ : Form r) (o : Orbit 0 x) :
    contribution hdim x θ o =
      -((-1 : ℝ) ^ (axis hdim x o).val) •
        ∫ z in strictOrthant
          (faceIndices (ForestGlobalGraphStokes.radialIndices hdim x) (axis hdim x o)),
          facePullback θ (axis hdim x o) 0 z (standardBasis r) := by
  unfold contribution
  rw [integral_orthant_eq_strictOrthant]

/-- Exhaustive disjoint partition of the literal signed face sum. -/
theorem lowerFaces_eq_sum_kinds (θ : Form r) :
    OrientedOrthantAssembly.lowerFaces θ (ForestGlobalGraphStokes.radialIndices hdim x) =
      ∑ k : Kind, ∑ o : Orbit 0 x,
        if kind 0 x o = k then contribution hdim x θ o else 0 := by
  rw [lowerFaces_eq_sum_orbits, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  simp

end Stokes

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestRadialFaceClassification
