import EnvelopingIsomorphism.Deformation.MainPurePhysicalFace

/-! Finite original-chart and pure-orbit reassembly on one physical two-point
boundary face. All source transfer, orbit uniqueness and L1 are derived. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.MainPureOrbitAssembly
open Kontsevich Configuration ForestRadialFaceClassification ForestRadialClusterLabels
open PureForestSimpleCluster (lower upper)
open MixedPairedCoreData MainPurePhysicalFace OrientedFormChangeVariables
open Set MeasureTheory BoxStokes
open scoped Classical
variable {n m r : ℕ} {hdim : GraphForms.dimension n m = r+1}
  {es : Fin r → GraphForms.Edge n m} (P : PairedData hdim es) (F : FaceData m)

theorem pure_orbit_eq_of_endpoints (x : Compactification (0 : Fin (n+1)) m)
    (o p : Orbit 0 x) (ho : kind 0 x o = .pureBoundary) (hp : kind 0 x p = .pureBoundary)
    (hl : lower x o = lower x p) (hu : upper x o = upper x p) : o = p := by
  apply MainRealSupportOrbit.orbit_eq_of_representative_mask x o p
  rw [← MainPureFixedChartImage.collisionMask_eq x o ho,
    ← MainPureFixedChartImage.collisionMask_eq x p hp,hl,hu]

def orbitSum (j : P.charts) : ℝ :=
  ∑ o : Orbit 0 j.val,
    if kind 0 j.val o = .pureBoundary ∧ lower j.val o = F.l ∧ upper j.val o = F.u then
      PairedData.orbitValue P j o else 0

def clusterValue : ℝ := ∑ j : P.charts, orbitSum P F j

theorem exists_orbit_of_cutoff_ne_zero (j : P.charts) (y : Coord r) (hy : y ∈ region hdim F)
    (hn : cutoff hdim F (P.partition j) y ≠ 0) :
    ∃ o : Orbit 0 j.val, kind 0 j.val o = .pureBoundary ∧ lower j.val o = F.l ∧ upper j.val o = F.u := by
  obtain ⟨D,hd⟩ := hy
  change (PureBoundaryClusterForms.dataCoarse D,PureBoundaryClusterForms.dataShape D) =
    (coordinates hdim F).symm y at hd
  have hcut : CompactDRAmbientPartition.cutoff 0 (P.partition j) D.boundaryPoint ≠ 0 := by
    simpa only [cutoff, ← hd, PureBoundaryFaceDR.ambient_data,
      CompactDRAmbientPartition.cutoff, CompactDRCoordinates.embedding, compactProjectDR] using hn
  obtain ⟨o,z,ho,hm,hz⟩ := MainFixedSimpleChartTransfer.pureBoundary_source hdim j.val D
    (mem_chart_of_cutoff_ne_zero P j _ hcut)
  have hb : boundaryClusterBlock (lower j.val o) (upper j.val o) = boundaryClusterBlock F.l F.u :=
    (boundaryLabels_eq_block 0 j.val (RealForestCoarsePositions.node j.val o)).symm.trans
      (MainFixedSimpleChartTransfer.boundaryLabels_of_mask j.val _ ∅ F.l F.u hm)
  exact ⟨o,ho,block_endpoints_eq F hb⟩

theorem orbitSum_eq_weighted_integral (j : P.charts) :
    orbitSum P F j = (-1 : ℝ)^F.a.val *
      ∫ y in region hdim F, cutoff hdim F (P.partition j) y * density (form hdim F es) y := by
  by_cases hex : ∃ o : Orbit 0 j.val,
      kind 0 j.val o = .pureBoundary ∧ lower j.val o = F.l ∧ upper j.val o = F.u
  · obtain ⟨o,ho,hl,hu⟩ := hex
    unfold orbitSum
    rw [Finset.sum_eq_single o]
    · rw [if_pos ⟨ho,hl,hu⟩]
      exact oriented_contribution_eq hdim F j.val o ho hl hu (P.partition j) (P.support j)
        es P.noLoops (P.localizer j) (P.localization j) (P.orientation j) (P.orientation_jacobian j)
    · intro p _ hpo
      split_ifs with hp
      · exact False.elim (hpo (pure_orbit_eq_of_endpoints j.val p o hp.1 ho
          (hp.2.1.trans hl.symm) (hp.2.2.trans hu.symm)))
      · rfl
    · simp
  · have hz : ∀ y ∈ region hdim F, cutoff hdim F (P.partition j) y = 0 := by
      intro y hy
      by_contra hn
      exact hex (exists_orbit_of_cutoff_ne_zero P F j y hy hn)
    have hi : (∫ y in region hdim F, cutoff hdim F (P.partition j) y * density (form hdim F es) y) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro y hy
      rw [hz y hy,zero_mul]
    rw [hi,mul_zero]
    unfold orbitSum
    apply Finset.sum_eq_zero
    intro o _
    rw [if_neg (fun ho ↦ hex ⟨o,ho⟩)]

theorem integrableOn_weighted_density (j : P.charts) :
    IntegrableOn (fun y ↦ cutoff hdim F (P.partition j) y * density (form hdim F es) y) (region hdim F) := by
  by_cases hex : ∃ o : Orbit 0 j.val,
      kind 0 j.val o = .pureBoundary ∧ lower j.val o = F.l ∧ upper j.val o = F.u
  · obtain ⟨o,ho,hl,hu⟩ := hex
    exact MainPurePhysicalFace.integrableOn_weighted_density hdim F j.val o ho hl hu
      (P.partition j) (P.support j) es P.noLoops (P.localizer j) (P.localization j)
      (P.regular j).1.continuous (P.regular j).2 (P.orientation j) (P.orientation_jacobian j)
  · refine (integrableOn_zero : IntegrableOn (fun _ : Coord r ↦ (0 : ℝ)) (region hdim F)).congr_fun ?_
      (measurableSet_region hdim F)
    intro y hy
    have hz : cutoff hdim F (P.partition j) y = 0 := by
      by_contra hn
      exact hex (exists_orbit_of_cutoff_ne_zero P F j y hy hn)
    simp only [hz,zero_mul]

theorem clusterValue_eq_integral :
    clusterValue P F = (-1 : ℝ)^F.a.val * ∫ y in region hdim F, density (form hdim F es) y := by
  unfold clusterValue
  simp_rw [orbitSum_eq_weighted_integral]
  rw [← Finset.mul_sum, ← integral_finsetSum _ (fun j _ ↦ integrableOn_weighted_density P F j)]
  congr 1
  apply setIntegral_congr_fun (measurableSet_region hdim F)
  intro y hy
  dsimp only
  rw [← Finset.sum_mul, sum_cutoff hdim F P.partition y hy,one_mul]

end EnvelopingIsomorphism.Deformation.MainPureOrbitAssembly
