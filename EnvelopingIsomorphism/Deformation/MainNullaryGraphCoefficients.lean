import EnvelopingIsomorphism.Deformation.GraphBinaryPhysicalSubsetIndex
import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryGraphMatching
import EnvelopingIsomorphism.Deformation.Kontsevich.InfinityBoundaryGraphMatching
import EnvelopingIsomorphism.Deformation.Kontsevich.MainRealGraftPhysicalCoefficient

/-! Literal empty and full physical-subset coefficients. The nullary factor
is the actual multiplication graph, whose raw weight is one. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MainNullaryGraphCoefficients
open scoped Classical
open UniformBinaryGraphs GraphBinaryClusterSums GraphLabelledClusterCounting
open GraphBinaryGraftFibres GraphCanonicalBinaryWeights GraphAssociatorProfiles
open GraphBinaryPhysicalSubsetIndex KontsevichGraph.General

variable {a b N : ℕ}

theorem rawClusterCoefficient_self (r : Fin 2) (H : BinaryGraph (a+b) 3) :
    rawClusterCoefficient r H ⟨innerBlock a b,rfl⟩ =
      extractedCoefficient r (rawBinaryWeight a) (rawBinaryWeight b) H := by
  let e : ClusterFiber (innerBlock a b) (innerBlock a b) := ⟨Equiv.refl _,fun _ ↦ Iff.rfl⟩
  have he := graftProfile_same_cluster r (rawBinaryWeight a) (rawBinaryWeight b)
    (rawBinaryWeight_permuteInternal a) (rawBinaryWeight_permuteInternal b)
    H ⟨innerBlock a b,rfl⟩ (clusterRepresentative _ _) e
  simp only [graftProfile_eq_extractedCoefficient] at he
  simpa only [rawClusterCoefficient, e, Equiv.refl_symm, Graph.permuteInternal_refl] using he

def emptyNative (H : BinaryGraph N 3) :=
  nativeGraph (a := N) (b := 0) (castVertices (Nat.add_zero N).symm H)

def fullNative (H : BinaryGraph N 3) :=
  nativeGraph (a := 0) (b := N) (castVertices (Nat.zero_add N).symm H)

theorem empty_innerClosed (H : BinaryGraph N 3) (r : Fin 2) :
    (emptyNative H).InnerClosed (l := 1) r := by
  intro e
  exact Fin.elim0 e.1

theorem full_coarseDistinct (H : BinaryGraph N 3) (r : Fin 2) :
    (fullNative H).CoarseDistinct (l := 1) r := by
  intro v
  exact Fin.elim0 v

theorem coefficient_empty_eq (H : BinaryGraph N 3) (r : Fin 2) :
    coefficient H r ∅ =
      if hd : (emptyNative H).CoarseDistinct (l := 1) r then
        rawBinaryWeight N ((emptyNative H).extractedOuter (l := 1) r hd) else 0 := by
  rw [coefficient_eq_of_count (Nat.add_zero N) H r ⟨innerBlock N 0,rfl⟩ ∅
    (by simp [innerBlock]), rawClusterCoefficient_self]
  have hc := empty_innerClosed H r
  unfold extractedCoefficient
  change (if h : (emptyNative H).InnerClosed (l := 1) r ∧ (emptyNative H).CoarseDistinct (l := 1) r then _ else _) = _
  split_ifs <;> simp_all [rawBinaryWeight]
  rfl

theorem coefficient_full_eq (H : BinaryGraph N 3) (r : Fin 2) :
    coefficient H r Finset.univ =
      if hc : (fullNative H).InnerClosed (l := 1) r then
        rawBinaryWeight N ((fullNative H).extractedInner (m := 1) r hc) else 0 := by
  rw [coefficient_eq_of_count (Nat.zero_add N) H r ⟨innerBlock 0 N,rfl⟩ Finset.univ
    (by ext v; simp [innerBlock]),
    rawClusterCoefficient_self]
  have hd := full_coarseDistinct H r
  unfold extractedCoefficient
  change (if h : (fullNative H).InnerClosed (l := 1) r ∧ (fullNative H).CoarseDistinct (l := 1) r then _ else _) = _
  split_ifs <;> simp_all [rawBinaryWeight]
  rfl

theorem empty_outer_target (H : BinaryGraph N 3) (r : Fin 2)
    (v : Fin N) (j : Fin 2) :
    (emptyNative H).extractedOuterTarget (l := 1) r ⟨v,j⟩ =
      Sum.map id (graftBoundaryCollapse (l := 1) r) (H.target ⟨v,j⟩) := by
  change graftCollapse (a := N) (b := 0) (l := 1) r ((castGraph (graftArity_two (a := N) (b := 0)).symm H).target
    (graftOuterEdge (fun _ : Fin N ↦ 2) (fun _ : Fin 0 ↦ 2) ⟨v,j⟩)) = _
  rw [graftOuterEdge_mk,castGraph_target]
  simp only [Fin.cast_cast]
  change graftCollapse (a := N) (b := 0) (l := 1) r (H.target ⟨v,j⟩) = _
  cases ht : H.target ⟨v,j⟩ with
  | inl w =>
    change Sum.elim Sum.inl (fun _ ↦ Sum.inr r) ((finSumFinEquiv : Fin N ⊕ Fin 0 ≃ Fin (N+0)).symm w) = Sum.inl w
    have he : (finSumFinEquiv : Fin N ⊕ Fin 0 ≃ Fin (N+0)).symm w = Sum.inl w := by
      exact (finSumFinEquiv : Fin N ⊕ Fin 0 ≃ Fin (N+0)).symm_apply_eq.mpr rfl
    rw [he]
    rfl
  | inr w => rfl

open Kontsevich BoundaryGraphFaceFactorization BoundaryGraphOrderedCoordinates
open PureBoundaryGraphQuotient PureBoundaryGraphMatching

variable {l u : Fin 4}

def slot (hlu : l ≤ u) (hsize : shapeM l u = 2) : Fin 2 :=
  ⟨l.val,by
    have hs := shapeM_eq_sub hlu
    have hu := u.isLt
    omega⟩

theorem outside_count (hsize : shapeM l u = 2) : outsideM l u + 1 = 2 := by
  have hc := boundary_card_sum (l := l) (u := u)
  omega

theorem collapsedBoundary_eq (hlu : l ≤ u) (hsize : shapeM l u = 2) (j : Fin 3) :
    Fin.cast (outside_count hsize) (collapsedBoundary hlu j) =
      graftBoundaryCollapse (l := 1) (slot hlu hsize) j := by
  apply Fin.ext
  have hs := shapeM_eq_sub hlu
  have hl : l.val ≤ u.val := hlu
  have hc := boundary_card_sum (l := l) (u := u)
  have hj := j.isLt
  have hu := u.isLt
  unfold collapsedBoundary graftBoundaryCollapse
  split_ifs with hm hlt hle hlt hle
  all_goals simp only [Fin.val_cast,centerSlot_val,slot]
  all_goals try have hmem := (mem_boundaryClusterBlock l u j).mp hm
  all_goals try have hnot := mt (mem_boundaryClusterBlock l u j).mpr hm
  all_goals try omega
  all_goals
    have he : (outsideOrderedEnum l u ⟨j,hm⟩).val = 0 := by
      have ht := (outsideOrderedEnum l u ⟨j,hm⟩).isLt
      omega
    simp only [Fin.succAbove,Fin.castSucc,Fin.succ,centerSlot,Fin.lt_def,he]
    split_ifs <;> simp only [slot,Fin.val_castAdd,Fin.val_mk] at * <;> omega

variable {n : ℕ}

theorem cast_quotientTarget (hlu : l ≤ u) (hsize : shapeM l u = 2)
    (H : BinaryGraph (n+1) 3) (v : Fin (n+1)) (j : Fin 2) :
    (Equiv.sumCongr (Equiv.refl _) (finCongr (outside_count hsize)))
      (quotientTarget hlu H ⟨v,j⟩) =
      (emptyNative H).extractedOuterTarget (l := 1) (slot hlu hsize) ⟨v,j⟩ := by
  rw [empty_outer_target]
  unfold quotientTarget
  cases ht : H.target ⟨v,j⟩ with
  | inl w => rfl
  | inr w =>
    change Sum.inr (Fin.cast (outside_count hsize) (collapsedBoundary hlu w)) = _
    rw [collapsedBoundary_eq hlu hsize]
    rfl

theorem quotientDistinct_iff (hlu : l ≤ u) (hsize : shapeM l u = 2)
    (H : BinaryGraph (n+1) 3) :
    QuotientDistinct hlu H ↔ (emptyNative H).CoarseDistinct (l := 1) (slot hlu hsize) := by
  constructor
  · intro hd v j k he
    apply hd v
    apply (Equiv.sumCongr (Equiv.refl _) (finCongr (outside_count hsize))).injective
    rw [cast_quotientTarget hlu hsize,cast_quotientTarget hlu hsize]
    exact he
  · intro hd v j k he
    apply hd v
    change (emptyNative H).extractedOuterTarget (l := 1) (slot hlu hsize) ⟨v,j⟩ =
      (emptyNative H).extractedOuterTarget (l := 1) (slot hlu hsize) ⟨v,k⟩
    rw [← cast_quotientTarget hlu hsize,← cast_quotientTarget hlu hsize]
    exact congrArg _ he

def binaryQuotient (hlu : l ≤ u) (hsize : shapeM l u = 2)
    (H : BinaryGraph (n+1) 3) (hd : QuotientDistinct hlu H) : BinaryGraph (n+1) 2 :=
  (quotientGraph hlu H hd).reindex (Equiv.refl _) (finCongr (outside_count hsize).symm)

theorem binaryQuotient_eq (hlu : l ≤ u) (hsize : shapeM l u = 2)
    (H : BinaryGraph (n+1) 3) (hd : QuotientDistinct hlu H) :
    binaryQuotient hlu hsize H hd =
      (emptyNative H).extractedOuter (l := 1) (slot hlu hsize) ((quotientDistinct_iff hlu hsize H).mp hd) := by
  apply Graph.ext
  funext ⟨v,j⟩
  exact cast_quotientTarget hlu hsize H v j

theorem coefficient_empty_of_distinct (hlu : l ≤ u) (hsize : shapeM l u = 2)
    (H : BinaryGraph (n+1) 3) (hd : QuotientDistinct hlu H) :
    coefficient H (slot hlu hsize) ∅ = rawBinaryWeight (n+1) (binaryQuotient hlu hsize H hd) := by
  rw [coefficient_empty_eq,dif_pos ((quotientDistinct_iff hlu hsize H).mp hd),binaryQuotient_eq]

theorem coefficient_empty_of_not_distinct (hlu : l ≤ u) (hsize : shapeM l u = 2)
    (H : BinaryGraph (n+1) 3) (hd : ¬ QuotientDistinct hlu H) :
    coefficient H (slot hlu hsize) ∅ = 0 := by
  rw [coefficient_empty_eq,dif_neg (mt (quotientDistinct_iff hlu hsize H).mpr hd)]

theorem coefficient_empty_eq_canonicalQuotientWeight
    (hlu : l ≤ u) (hsize : shapeM l u = 2)
    (H : BinaryGraph (n+1) 3) (hd : QuotientDistinct hlu H)
    (hD : ∑ _ : Fin (n+1), 2 = GraphForms.dimension n (outsideM l u + 1)) :
    coefficient H (slot hlu hsize) ∅ =
      GeometricWeights.canonicalWeight (quotientGraph hlu H hd) hD := by
  rw [coefficient_empty_of_distinct hlu hsize H hd,
    MainRealGraftPhysicalCoefficient.canonicalWeight_eq_raw_cast (outside_count hsize)]
  rfl

end EnvelopingIsomorphism.Deformation.MainNullaryGraphCoefficients
