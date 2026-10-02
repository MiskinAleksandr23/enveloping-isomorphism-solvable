import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryGraphIntegral
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphOrderedDomains

/-! The increasing quotient chamber is genuinely the two-point pure-boundary
face: each quotient configuration constructs native primitive collision data,
and actual collision data gives an admissible quotient configuration. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryGraphDomain
open scoped Classical
open GraphForms PureBoundaryClusterForms PureBoundaryGraphQuotient
open BoundaryGraphFaceFactorization BoundaryGraphOrderedCoordinates
variable {n m : ℕ} {l u : Fin (m+1)}

lemma collapsedBoundary_lt_center (hlu : l ≤ u) (j : Fin m) (hj : j.val < l.val) :
    collapsedBoundary hlu j < centerSlot hlu := by
  have hn : j ∉ boundaryClusterBlock l u := by simp only [mem_boundaryClusterBlock]; omega
  rw [collapsedBoundary, dif_neg hn, succAbove_lt_center_iff, outsideOrderedEnum_val hlu]
  simp [hj]

lemma center_lt_collapsedBoundary (hlu : l ≤ u) (j : Fin m) (hj : u.val ≤ j.val) :
    centerSlot hlu < collapsedBoundary hlu j := by
  have hn : j ∉ boundaryClusterBlock l u := by simp only [mem_boundaryClusterBlock]; omega
  rw [collapsedBoundary, dif_neg hn, center_lt_succAbove_iff, outsideOrderedEnum_val hlu]
  change l.val ≤ (if j.val < l.val then j.val else j.val - (u.val - l.val))
  have hl : l.val ≤ u.val := hlu
  rw [if_neg (by omega)]
  omega

lemma collapsedBoundary_lt (hlu : l ≤ u) (j k : Fin m) (hjk : j < k)
    (hnot : ¬(j ∈ boundaryClusterBlock l u ∧ k ∈ boundaryClusterBlock l u)) :
    collapsedBoundary hlu j < collapsedBoundary hlu k := by
  by_cases hj : j ∈ boundaryClusterBlock l u
  · have hk : k ∉ boundaryClusterBlock l u := fun hk ↦ hnot ⟨hj,hk⟩
    rw [collapsedBoundary, dif_pos hj]
    apply center_lt_collapsedBoundary hlu k
    have hj' := (mem_boundaryClusterBlock l u j).mp hj
    have hk' : ¬(l.val ≤ k.val ∧ k.val < u.val) := by simpa only [mem_boundaryClusterBlock] using hk
    have hlt : j.val < k.val := hjk
    omega
  · by_cases hk : k ∈ boundaryClusterBlock l u
    · rw [show collapsedBoundary hlu k = centerSlot hlu by simp [collapsedBoundary, hk]]
      apply collapsedBoundary_lt_center hlu j
      have hk' := (mem_boundaryClusterBlock l u k).mp hk
      have hj' : ¬(l.val ≤ j.val ∧ j.val < u.val) := by simpa only [mem_boundaryClusterBlock] using hj
      have hlt : j.val < k.val := hjk
      omega
    · rw [collapsedBoundary, dif_neg hj, collapsedBoundary, dif_neg hk]
      apply Fin.strictMono_succAbove
      apply (outsideOrderedEnum_symm_strictMono (l := l) (u := u)).lt_iff_lt.mp
      simpa using hjk

variable (hlu : l ≤ u) (a b : Fin m)
  (ha : a ∈ boundaryClusterBlock l u) (hb : b ∈ boundaryClusterBlock l u)
  (hab : a < b) (hcard : (boundaryClusterBlock l u).card = 2)
  (hl : a.val = l.val) (hu : b.val + 1 = u.val)

include ha hb hab hcard in
lemma mem_block_iff (j : Fin m) : j ∈ boundaryClusterBlock l u ↔ j = a ∨ j = b := by
  have hp : ({a,b} : Finset (Fin m)) = boundaryClusterBlock l u := by
    apply Finset.eq_of_subset_of_card_le
    · intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact ha
      · have hk' : k = b := Finset.mem_singleton.mp hk
        simpa [hk'] using hb
    · simp [hcard, hab.ne]
  rw [← hp]
  simp

/-- Every actual quotient configuration determines the actual pure-boundary
primitive data, with the prescribed endpoint shapes zero and one. -/
def datum (x : Coordinates n (outsideM l u + 1)) (hx : Admissible x) :
    PureBoundaryClusterData (0 : Fin (n+1)) m l u a b where
  center := x.2 (centerSlot hlu)
  interior j := ⟨interiorPoint j x, by
    cases j using Fin.cases with
    | zero => simp [interiorPoint]
    | succ j => exact hx.1 j⟩
  boundaryBase j := x.2 (collapsedBoundary hlu j)
  boundaryVelocity j := if j = b then 1 else 0
  left_endpoint := hl
  right_endpoint := hu
  endpoint_lt := hab
  interior_injective := by
    intro j k h
    apply hx.2.1
    exact congrArg (fun z : UpperHalfPlane ↦ (z : ℂ)) h
  interior_normalized := by apply UpperHalfPlane.ext; rfl
  boundaryBase_eq_center j hj := by rw [collapsedBoundary, dif_pos hj]
  boundaryBase_lt_center j hj := hx.2.2 (collapsedBoundary_lt_center hlu j hj)
  center_lt_boundaryBase j hj := hx.2.2 (center_lt_collapsedBoundary hlu j hj)
  boundaryBase_lt j k hjk hnot := hx.2.2 (collapsedBoundary_lt hlu j k hjk hnot)
  boundaryVelocity_zero_off j hj := by
    have hne : j ≠ b := fun h ↦ hj (h ▸ hb)
    simp [hne]
  boundaryVelocity_strictMono_on j k hj hk hjk := by
    have hj' := (mem_block_iff a b ha hb hab hcard j).mp hj
    have hk' := (mem_block_iff a b ha hb hab hcard k).mp hk
    rcases hj' with rfl | rfl <;> rcases hk' with rfl | rfl
    · exact (lt_irrefl _ hjk).elim
    · simp [hab.ne]
    · exact (not_lt_of_gt hab hjk).elim
    · exact (lt_irrefl _ hjk).elim
  boundaryVelocity_left := by simp [hab.ne]
  boundaryVelocity_right := by simp

lemma orderedCoarseCoordinates_center (c : Coarse n (boundaryClusterBlock l u)) :
    (orderedCoarseCoordinates hlu c).2 (centerSlot hlu) = c.2.1 := by
  change (coarseCoordinates c).2 ((coarsePermutation hlu).symm (centerSlot hlu)) = _
  rw [← coarsePermutation_center hlu, Equiv.symm_apply_apply]
  rfl

lemma orderedCoarseCoordinates_outside (c : Coarse n (boundaryClusterBlock l u))
    (j : Fin (outsideM l u)) :
    (orderedCoarseCoordinates hlu c).2 ((centerSlot hlu).succAbove j) =
      c.2.2 ((outsideOrderedEnum l u).symm j) := by
  have h := orderedCoarseCoordinates_boundary hlu c ((outsideOrderedEnum l u).symm j).val
  simpa [collapsedBoundary, ((outsideOrderedEnum l u).symm j).property,
    boundaryBaseCLM, outsideCLM, -mem_boundaryClusterBlock] using h

theorem datum_quotient (x : Coordinates n (outsideM l u + 1)) (hx : Admissible x) :
    orderedCoarseCoordinates hlu (dataCoarse (datum hlu a b ha hb hab hcard hl hu x hx)) = x := by
  apply Prod.ext
  · rfl
  · funext j
    cases j using Fin.succAboveCases (centerSlot hlu) with
    | x => rw [orderedCoarseCoordinates_center]; rfl
    | p j =>
      rw [orderedCoarseCoordinates_outside]
      change x.2 (collapsedBoundary hlu ((outsideOrderedEnum l u).symm j).val) = _
      simp [collapsedBoundary, ((outsideOrderedEnum l u).symm j).property, -mem_boundaryClusterBlock]

variable {a b}

theorem dataCoarse_admissible (D : PureBoundaryClusterData (0 : Fin (n+1)) m l u a b) :
    Admissible (orderedCoarseCoordinates hlu (dataCoarse D)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    exact (D.interior j.succ).im_pos
  · intro j k h
    have hpos (j : Fin (n+1)) :
        interiorPoint j (orderedCoarseCoordinates hlu (dataCoarse D)) = (D.interior j : ℂ) := by
      cases j using Fin.cases with
      | zero => simp [D.interior_normalized, interiorPoint]
      | succ j => rfl
    apply D.interior_injective
    apply UpperHalfPlane.ext
    simpa only [hpos] using h
  · intro j k hjk
    cases j using Fin.succAboveCases (centerSlot hlu) with
    | x =>
      cases k using Fin.succAboveCases (centerSlot hlu) with
      | x => exact (lt_irrefl _ hjk).elim
      | p k =>
        rw [orderedCoarseCoordinates_center, orderedCoarseCoordinates_outside]
        apply D.center_lt_boundaryBase
        have hk := (center_lt_succAbove_iff hlu k).mp hjk
        rw [outsideOrderedEnum_symm_val hlu, if_neg (not_lt_of_ge hk)]
        have hle : l.val ≤ u.val := hlu
        omega
    | p j =>
      cases k using Fin.succAboveCases (centerSlot hlu) with
      | x =>
        rw [orderedCoarseCoordinates_outside, orderedCoarseCoordinates_center]
        apply D.boundaryBase_lt_center
        have hj := (succAbove_lt_center_iff hlu j).mp hjk
        simp [outsideOrderedEnum_symm_val hlu, hj]
      | p k =>
        rw [orderedCoarseCoordinates_outside, orderedCoarseCoordinates_outside]
        exact D.boundaryBase_lt _ _
          (outsideOrderedEnum_symm_strictMono ((Fin.strictMono_succAbove (centerSlot hlu)).lt_iff_lt.mp hjk))
          (fun h ↦ ((outsideOrderedEnum l u).symm j).property h.1)

/-- The native face locus is the range of actual primitive collision data. -/
def nativeDomain (a b : Fin m) : Set (Face n (boundaryClusterBlock l u) a b) :=
  Set.range (fun D : PureBoundaryClusterData (0 : Fin (n+1)) m l u a b ↦
    (dataCoarse D, dataShape D))

include ha hb hab hcard hl hu in
theorem nativeDomain_eq_preimage :
    nativeDomain (n := n) (l := l) (u := u) a b =
      (twoPointCoordinates hlu a b ha hb hab.ne hcard) ⁻¹'
        admissibleSet n (outsideM l u + 1) := by
  ext y
  constructor
  · rintro ⟨D,rfl⟩
    exact dataCoarse_admissible hlu D
  · intro hy
    let x := twoPointCoordinates hlu a b ha hb hab.ne hcard y
    have hx : Admissible x := hy
    refine ⟨datum hlu a b ha hb hab hcard hl hu x hx, ?_⟩
    apply (twoPointCoordinates hlu a b ha hb hab.ne hcard).injective
    exact datum_quotient hlu a b ha hb hab hcard hl hu x hx

include ha hb hab hcard hl hu in
/-- The precise real Lebesgue chamber in the integral endpoint is exactly the
image of the actual native primitive face, not an assumed replacement domain. -/
theorem realDomain_eq_native_preimage :
    GeometricWeights.realDomain n (outsideM l u + 1) =
      (PureBoundaryGraphIntegral.faceCoordinates hlu a b ha hb hab.ne hcard).symm ⁻¹'
        nativeDomain (n := n) (l := l) (u := u) a b := by
  rw [nativeDomain_eq_preimage hlu ha hb hab hcard hl hu]
  ext x
  change Admissible ((realCoordinates n (outsideM l u + 1)).symm x) ↔
    Admissible (twoPointCoordinates hlu a b ha hb hab.ne hcard
      ((PureBoundaryGraphIntegral.faceCoordinates hlu a b ha hb hab.ne hcard).symm x))
  simp only [PureBoundaryGraphIntegral.faceCoordinates, ContinuousLinearEquiv.symm_trans_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  rfl

end EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryGraphDomain
