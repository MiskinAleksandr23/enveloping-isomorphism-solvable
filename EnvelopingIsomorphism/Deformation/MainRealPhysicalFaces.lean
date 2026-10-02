import EnvelopingIsomorphism.Deformation.MainRealMaskClassification
import EnvelopingIsomorphism.Deformation.MainRealValenceVanishing

/-! One common finite physical-face index for every original chart. The
subset and the two actual boundary endpoints determine the native orbit;
its full ordered integral uses anchors chosen solely from the subset. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MainRealPhysicalFaces
open Kontsevich Configuration ForestRadialFaceClassification
open RealForestCoarsePositions (labelsSet node)
open RealForestSimpleCluster (lower upper)
open MainScalarBoundaryAssembly MainClassifiedFaceAssembly
open MainRealOrderedChartIntegral MainRealMaskClassification
open BoundaryGraphFaceFactorization BoundaryGraphOrderedIntegrals
open MeasureTheory
open scoped Classical BigOperators

abbrev Key (n : ℕ) := {p : Finset (Fin (n+2)) × Fin 4 × Fin 4 //
  p.1.Nonempty ∧ p.1ᶜ.Nonempty ∧ p.2.1 ≤ p.2.2 ∧ (boundaryClusterBlock p.2.1 p.2.2).card = 2}

namespace Key
variable {n : ℕ} (K : Key n)
abbrev S := K.val.1
abbrev l := K.val.2.1
abbrev u := K.val.2.2
def inside : Fin (n+2) := K.S.min' K.property.1
def outside : Fin (n+2) := K.Sᶜ.min' K.property.2.1
theorem inside_mem : K.inside ∈ K.S := Finset.min'_mem _ _
theorem outside_not_mem : K.outside ∉ K.S := by
  exact Finset.mem_compl.mp (Finset.min'_mem K.Sᶜ K.property.2.1)
theorem block_nonempty : (boundaryClusterBlock K.l K.u).Nonempty :=
  Finset.card_pos.mp (by rw [K.property.2.2.2]; decide)
theorem block_lt : K.l < K.u := by
  obtain ⟨j,hj⟩ := K.block_nonempty
  have h := (mem_boundaryClusterBlock K.l K.u j).mp hj
  change K.l.val < K.u.val
  exact lt_of_le_of_lt h.1 h.2
theorem degree_eq : shapeDegree K.inside K.S K.l K.u + coarseDegree K.outside K.S K.l K.u =
    GraphForms.dimension (n+1) 2 := by
  rw [face_degree_eq K.inside_mem K.outside_not_mem]
  simp [GraphForms.dimension]
  omega
end Key

variable {n : ℕ} {H : UniformBinaryGraphs.BinaryGraph (n+2) 3} (P : MainPartition H) (j : P.charts)

abbrev Surviving := {o : Orbit 0 j.val // kind 0 j.val o = .properReal ∧
  (boundaryClusterBlock (lower j.val o) (upper j.val o)).card = 2}

def keyOfOrbit (o : Surviving P j) : Key n :=
  ⟨⟨labelsSet j.val o.val,lower j.val o.val,upper j.val o.val⟩,by
    obtain ⟨a,b,ha,hb⟩ := ForestRadialClusterLabels.properReal_anchors 0 j.val (node j.val o.val)
      ((kind_representative 0 j.val o.val).trans o.property.1)
    exact ⟨⟨a,ha⟩,⟨b,Finset.mem_compl.mpr hb⟩,
      ForestRadialClusterLabels.block_order 0 j.val (node j.val o.val),o.property.2⟩⟩

theorem keyOfOrbit_injective : Function.Injective (keyOfOrbit P j) := by
  intro o p he
  have hS := congrArg (fun K : Key n => K.S) he
  have hl := congrArg (fun K : Key n => K.l) he
  have hu := congrArg (fun K : Key n => K.u) he
  change labelsSet j.val o.val = labelsSet j.val p.val at hS
  change lower j.val o.val = lower j.val p.val at hl
  change upper j.val o.val = upper j.val p.val at hu
  apply Subtype.ext
  apply MainRealSupportOrbit.orbit_eq_of_representative_mask
  rw [← MainRealFixedChartImage.collisionMask_eq j.val o.val o.property.1,
    ← MainRealFixedChartImage.collisionMask_eq j.val p.val p.property.1]
  rw [hS,hl,hu]

def physicalEdges (H : UniformBinaryGraphs.BinaryGraph (n+2) 3) (K : Key n) :
    Fin (shapeDegree K.inside K.S K.l K.u + coarseDegree K.outside K.S K.l K.u) → Edge (n+2) 3 :=
  fun t => let e := mainEdges H (finCongr K.degree_eq t); (e.source,e.target)

def weightedValue (K : Key n) : ℝ :=
  -(∫ z in MainRealPartitionReassembly.FaceRegion,
    MainRealPartitionReassembly.weight K.inside_mem K.outside_not_mem K.property.2.2.1 P.partition j z *
      orderedRealDensity (physicalEdges H K) K.property.2.2.1 z ∂volume.prod volume)

/-- A surviving original Stokes orbit is exactly the weighted physical face
selected by its subset and boundary endpoints, with common subset anchors. -/
theorem orbitValue_eq_weightedValue (o : Surviving P j) :
    orbitValue P j o.val = weightedValue P j (keyOfOrbit P j o) := by
  let K := keyOfOrbit P j o
  have h := oriented_contribution_eq_ordered_integral (main_dimension n) j.val o.val
    K.inside K.outside K.inside_mem K.outside_not_mem P.partition j o.property.1 K.block_nonempty
    (P.support j) (mainEdges H) (mainEdges_noLoops H) (P.localizer j) (P.localization j)
    (P.orientation j) (P.orientation_jacobian j)
  rw [RealForestExplicitTransfer.main_radius_sign (main_dimension n),neg_one_mul] at h
  have hedge : MainRealOrderedChartIntegral.nativeEdges (main_dimension n) j.val o.val
      K.inside K.outside K.inside_mem K.outside_not_mem
      (fun j => ForestPositiveGraphForms.forestEdge 0 (mainEdges H j) (mainEdges_noLoops H j)) = physicalEdges H K := by
    funext t
    simp [MainRealOrderedChartIntegral.nativeEdges,physicalEdges,ForestPositiveGraphForms.forestEdge]
  rw [hedge] at h
  exact h

theorem exists_orbit_of_weight_ne_zero (K : Key n)
    (z : MainRealPartitionReassembly.RealSpace (i := K.outside) (a := K.inside) (S := K.S) (l := K.l) (u := K.u))
    (hz : z ∈ MainRealPartitionReassembly.FaceRegion)
    (hw : MainRealPartitionReassembly.weight K.inside_mem K.outside_not_mem K.property.2.2.1 P.partition j z ≠ 0) :
    ∃ o : Surviving P j, keyOfOrbit P j o = K := by
  let D := (MainRealPartitionReassembly.freePoint K.inside_mem K.outside_not_mem K.property.2.2.1 ⟨z,hz⟩).datum
  have hρ : CompactDRAmbientPartition.cutoff 0 (P.partition j) (anchorHomeomorph K.outside 0 D.boundaryPoint) ≠ 0 := by
    rw [MainRealPartitionReassembly.weight_eq _ _ _ _ _ _ hz,
      MainRealPartitionReassembly.facePoint_eq_boundaryPoint] at hw
    exact hw
  obtain ⟨o,w,ho,hS,hl,hu,hpoint⟩ := properReal_source_of_cutoff P j D K.block_lt hρ
  have hc : (boundaryClusterBlock (lower j.val o) (upper j.val o)).card = 2 := by
    rw [hl,hu]
    exact K.property.2.2.2
  exact ⟨⟨o,ho,hc⟩,Subtype.ext (Prod.ext hS (Prod.ext hl hu))⟩

/-- A physical face missing from this chart's orbit list has identically
zero original weight, derived from actual chart transfer. -/
theorem weightedValue_eq_zero_of_not_mem_range (K : Key n)
    (hK : K ∉ Set.range (keyOfOrbit P j)) : weightedValue P j K = 0 := by
  unfold weightedValue
  rw [neg_eq_zero]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro z hz
  have hw : MainRealPartitionReassembly.weight K.inside_mem K.outside_not_mem K.property.2.2.1 P.partition j z = 0 := by
    by_contra hw
    exact hK (exists_orbit_of_weight_ne_zero P j K z hz hw)
  rw [hw,zero_mul]

theorem sum_surviving_eq_sum_weightedValue :
    (∑ o : Surviving P j, orbitValue P j o.val) = ∑ K : Key n, weightedValue P j K :=
  Fintype.sum_of_injective (keyOfOrbit P j) (keyOfOrbit_injective P j) _ _
    (weightedValue_eq_zero_of_not_mem_range P j) (orbitValue_eq_weightedValue P j)

theorem sum_surviving_eq_classified :
    (∑ o : Surviving P j, orbitValue P j o.val) =
      ∑ o : Orbit 0 j.val, if kind 0 j.val o = .properReal then orbitValue P j o else 0 := by
  apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
  · intro o ho
    by_cases hk : kind 0 j.val o = .properReal
    · rw [if_pos hk]
      apply MainRealValenceVanishing.main_orbitValue_eq_zero P j o hk
      intro hc
      exact ho ⟨⟨o,hk,hc⟩,rfl⟩
    · exact if_neg hk
  · intro o
    exact (if_pos o.property.1).symm

def physicalValue (H : UniformBinaryGraphs.BinaryGraph (n+2) 3) (K : Key n) : ℝ :=
  -(∫ z in MainRealPartitionReassembly.FaceRegion,
    orderedRealDensity (physicalEdges H K) K.property.2.2.1 z ∂volume.prod volume)

theorem physicalEdges_noLoops (K : Key n) (t) :
    (physicalEdges H K t).2 ≠ Sum.inl (physicalEdges H K t).1 :=
  mainEdges_noLoops H (finCongr K.degree_eq t)

/-- Whole physical integrability is unconditional. If the density is
nonzero somewhere, its actual graph forces the factorization hypotheses;
otherwise the integrand vanishes pointwise. -/
theorem integrableOn_physicalDensity (K : Key n) :
    IntegrableOn (orderedRealDensity (physicalEdges H K) K.property.2.2.1)
      MainRealPartitionReassembly.FaceRegion (volume.prod volume) := by
  by_cases hn : ∃ z ∈ MainRealPartitionReassembly.FaceRegion,
      orderedRealDensity (physicalEdges H K) K.property.2.2.1 z ≠ 0
  · obtain ⟨z,hz,hn⟩ := hn
    have hy := (orderedRealFace_open_iff K.inside_mem K.outside_not_mem K.property.2.2.1 z).mpr hz
    have hc := BoundaryGraphDimensionVanishing.internal_count_eq_of_nativeFaceDensity_ne_zero
      (physicalEdges H K) (physicalEdges_noLoops K) (orderedRealFace K.property.2.2.1 z) hy hn
    have hout := BoundaryGraphAdmissibility.noOutgoing_of_nativeFaceDensity_ne_zero
      (physicalEdges H K) (physicalEdges_noLoops K) (orderedRealFace K.property.2.2.1 z) hy hn
    exact MainRealPartitionReassembly.integrableOn_orderedRealDensity K.inside_mem K.outside_not_mem
      K.property.2.2.1 (physicalEdges H K) hc hout (physicalEdges_noLoops K)
  · apply (integrableOn_zero : IntegrableOn (fun _ => (0 : ℝ)) _ _).congr_fun
    · intro z hz
      exact (not_ne_iff.mp (fun h => hn ⟨z,hz,h⟩)).symm
    · exact MainRealPartitionReassembly.measurableSet_faceRegion

/-- The whole original finite partition is reassembled for a fixed
physical face before its graph integral is evaluated. -/
theorem sum_weightedValue_eq_physicalValue (K : Key n) :
    (∑ j : P.charts, weightedValue P j K) = physicalValue H K := by
  simp only [weightedValue,physicalValue,Finset.sum_neg_distrib]
  congr 1
  exact MainRealPartitionReassembly.sum_integral_weight_mul K.inside_mem K.outside_not_mem
    K.property.2.2.1 P.partition _ (integrableOn_physicalDensity K)

/-- Complete proper-real assembly from the original finite Stokes partition
to one unweighted physical integral per nonempty proper subset and adjacent
pair of boundary labels. No geometric matching premise remains. -/
theorem nativeKind_properReal_eq_sum_physicalValue :
    nativeKindBoundary P .properReal = ∑ K : Key n, physicalValue H K := by
  calc
    nativeKindBoundary P .properReal =
        ∑ j : P.charts, ∑ o : Orbit 0 j.val,
          if kind 0 j.val o = .properReal then orbitValue P j o else 0 := by
      rw [← transportedKind_eq_nativeKind P (defaultCoordinates P) .properReal]
      simp only [transportedKind,transportedValue_eq_orbitValue]
    _ = ∑ j : P.charts, ∑ K : Key n, weightedValue P j K := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← sum_surviving_eq_classified, sum_surviving_eq_sum_weightedValue]
    _ = ∑ K : Key n, ∑ j : P.charts, weightedValue P j K := Finset.sum_comm
    _ = _ := by simp_rw [sum_weightedValue_eq_physicalValue]

end EnvelopingIsomorphism.Deformation.MainRealPhysicalFaces
