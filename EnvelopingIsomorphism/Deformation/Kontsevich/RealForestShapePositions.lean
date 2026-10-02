import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestCoarsePositions

/-! Actual simple real-cluster shape positions obtained from the residual
forest insertion below the unique fixed collapsed node. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.RealForestShapePositions
open Configuration ExtractedForestParameters ExtractedForestFrames ExtractedForestChildShapes
open ForestRadialFaceClassification ForestRadialClusterLabels ForestInsertionDifference
open AncestorScaleRatios ComplexConjugate
open PairedForestCoarsePositions (parameters radius_reflect increment_reflect openConditions)
open RealForestCoarsePositions (node node_fixed labelsSet radius_pos_of_ne)
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n+1)) m)
  (o : ForestRadialFaceClassification.Orbit 0 x) (ho : RealForestCoarsePositions.IsFixed x o)
  (z : ForestRadialFaceLocalization.source hdim x o)

abbrev Tree := SubtreeForestInsertion.Tree (tree 0 x) (node x o)

def positions (j : DoubledLabel (n+1) m) : ℂ :=
  branchUnit (tree 0 x) (parameters hdim x o z).1 (parameters hdim x o z).2
    (node x o) (canonicalLeaf 0 x j)

def leaf (j : DoubledLabel (n+1) m) (hj : j ∈ (node x o).val) : Tree x o :=
  ⟨canonicalLeaf 0 x j, (le_canonicalLeaf_iff 0 x _ _).mpr hj⟩

def radii : Tree x o → ℝ :=
  SubtreeForestInsertion.radius (tree 0 x) (node x o) (parameters hdim x o z).1

def increments : Tree x o → ℂ :=
  SubtreeForestInsertion.increment (tree 0 x) (node x o) (parameters hdim x o z).2

include ho

theorem radii_pos (v : Tree x o) : 0 < radii hdim x o z v := by
  by_cases hv : v = ⊥
  · subst v
    rw [radii, SubtreeForestInsertion.radius_root]
    exact zero_lt_one
  · rw [radii, SubtreeForestInsertion.radius_nonroot _ _ _ _ hv]
    exact radius_pos_of_ne hdim x o ho z v.val (fun h ↦ hv (Subtype.ext h))

theorem positions_reflect (j : DoubledLabel (n+1) m) :
    positions hdim x o z (doubledReflection j) = conj (positions hdim x o z j) := by
  have h := ReflectedForestInsertion.branchUnit_reflect (tree 0 x) (reflection 0 x)
    (parameters hdim x o z).1 (radius_reflect hdim x o z)
    (parameters hdim x o z).2 (increment_reflect hdim x o z)
    (node x o) (canonicalLeaf 0 x j)
  rw [node_fixed x o ho] at h
  simpa only [positions, reflection, canonicalLeaf_reflect] using h

theorem positions_sub (j k : DoubledLabel (n+1) m)
    (hj : j ∈ (node x o).val) (hk : k ∈ (node x o).val) :
    positions hdim x o z j - positions hdim x o z k =
      scale (radii hdim x o z) (leaf x o j hj ⊓ leaf x o k hk) •
        unitDifference (tree 0 x) (parameters hdim x o z).1 (parameters hdim x o z).2
          (canonicalLeaf 0 x j) (canonicalLeaf 0 x k) := by
  have h := position_sub_position (Tree x o) (radii hdim x o z) (increments hdim x o z)
    (leaf x o j hj) (leaf x o k hk)
  dsimp only [Tree, radii, increments] at h
  rw [SubtreeForestInsertion.position_eq_branchUnit, SubtreeForestInsertion.position_eq_branchUnit,
    ← SubtreeForestInsertion.unitDifference_eq] at h
  exact h

theorem positions_injective_on : Set.InjOn (positions hdim x o z) (node x o).val := by
  intro j hj k hk he
  by_contra hne
  have hu := (openConditions hdim x o z).1 ⟨(k,j), Ne.symm hne⟩
  change unitDifference (tree 0 x) (parameters hdim x o z).1 (parameters hdim x o z).2
    (canonicalLeaf 0 x j) (canonicalLeaf 0 x k) ≠ 0 at hu
  have hs := scale_pos (radii hdim x o z) (radii_pos hdim x o ho z)
    (leaf x o j hj ⊓ leaf x o k hk)
  have h := positions_sub hdim x o ho z j k hj hk
  rw [he, sub_self] at h
  exact (smul_ne_zero hs.ne' hu) h.symm

theorem positions_upper_im_pos (j : Fin (n+1)) (hj : j ∈ labelsSet x o) :
    0 < (positions hdim x o z (Sum.inl (Sum.inl j))).im := by
  have hju := (mem_interiorLabels 0 x _ _).mp hj
  have hjr := (fixed_mem_mirror_iff 0 x _ (node_fixed x o ho) j).mpr hju
  have hs := scale_pos (radii hdim x o z) (radii_pos hdim x o ho z)
    (leaf x o (Sum.inl (Sum.inl j)) hju ⊓ leaf x o (Sum.inr j) hjr)
  have hp := (openConditions hdim x o z).2.1 j
  change 0 < (unitDifference (tree 0 x) (parameters hdim x o z).1 (parameters hdim x o z).2
    (canonicalLeaf 0 x (Sum.inl (Sum.inl j))) (canonicalLeaf 0 x (Sum.inr j))).im at hp
  have h := congrArg Complex.im (positions_sub hdim x o ho z _ _ hju hjr)
  have href := positions_reflect hdim x o ho z (Sum.inl (Sum.inl j))
  change positions hdim x o z (Sum.inr j) = conj (positions hdim x o z (Sum.inl (Sum.inl j))) at href
  rw [href] at h
  simp only [Complex.sub_im, Complex.conj_im, Complex.real_smul, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at h
  have := mul_pos hs hp
  linarith

theorem positions_boundary_lt (j k : Fin m) (hjk : j < k)
    (hj : Sum.inl (Sum.inr j) ∈ (node x o).val) (hk : Sum.inl (Sum.inr k) ∈ (node x o).val) :
    (positions hdim x o z (Sum.inl (Sum.inr j))).re <
      (positions hdim x o z (Sum.inl (Sum.inr k))).re := by
  have hs := scale_pos (radii hdim x o z) (radii_pos hdim x o ho z)
    (leaf x o _ hk ⊓ leaf x o _ hj)
  have hp := (openConditions hdim x o z).2.2 j k hjk
  change 0 < (unitDifference (tree 0 x) (parameters hdim x o z).1 (parameters hdim x o z).2
    (canonicalLeaf 0 x (Sum.inl (Sum.inr k))) (canonicalLeaf 0 x (Sum.inl (Sum.inr j)))).re at hp
  have h := congrArg Complex.re (positions_sub hdim x o ho z _ _ hk hj)
  simp only [Complex.sub_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
  exact sub_pos.mp (h ▸ mul_pos hs hp)

end EnvelopingIsomorphism.Deformation.Kontsevich.RealForestShapePositions
