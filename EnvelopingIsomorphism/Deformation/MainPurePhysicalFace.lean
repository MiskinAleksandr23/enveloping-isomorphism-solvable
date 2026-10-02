import EnvelopingIsomorphism.Deformation.MainPureFixedChartIntegrability
import EnvelopingIsomorphism.Deformation.MainPurePartitionReassembly
import EnvelopingIsomorphism.Deformation.MixedPairedCoreData

/-! A two-boundary-label pure face with coordinates independent of every
original forest center. These coordinates permit literal finite reassembly. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.MainPurePhysicalFace
open Kontsevich Configuration ForestRadialFaceClassification
open BoundaryGraphFaceFactorization BoundaryGraphOrderedCoordinates
open Set MeasureTheory BoxStokes OrientedFormChangeVariables
open scoped Classical

structure FaceData (m : ℕ) where
  l : Fin (m+1)
  u : Fin (m+1)
  a : Fin m
  b : Fin m
  ordered : l ≤ u
  left_mem : a ∈ boundaryClusterBlock l u
  right_mem : b ∈ boundaryClusterBlock l u
  endpoints : a < b
  left_eq : a.val = l.val
  right_eq : b.val + 1 = u.val
  card_eq : (boundaryClusterBlock l u).card = 2

variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1) (F : FaceData m)

theorem block_endpoints_eq {l u : Fin (m+1)}
    (he : boundaryClusterBlock l u = boundaryClusterBlock F.l F.u) : l = F.l ∧ u = F.u := by
  have ha : F.a ∈ boundaryClusterBlock l u := he.symm ▸ F.left_mem
  have hb : F.b ∈ boundaryClusterBlock l u := he.symm ▸ F.right_mem
  have hla := (mem_boundaryClusterBlock l u F.a).mp ha
  have hub := (mem_boundaryClusterBlock l u F.b).mp hb
  have hlm : l.val < m := lt_of_le_of_lt hla.1 F.a.isLt
  have hu0 : 0 < u.val := by omega
  have hum : u.val - 1 < m := by have hh := u.isLt; omega
  have hlam : (⟨l.val,hlm⟩ : Fin m) ∈ boundaryClusterBlock F.l F.u := by
    rw [← he]
    simp only [mem_boundaryClusterBlock]
    omega
  have hubm : (⟨u.val-1,hum⟩ : Fin m) ∈ boundaryClusterBlock F.l F.u := by
    rw [← he]
    simp only [mem_boundaryClusterBlock]
    omega
  have hfla := (mem_boundaryClusterBlock F.l F.u _).mp hlam
  have hfub := (mem_boundaryClusterBlock F.l F.u _).mp hubm
  have hh := F.left_eq
  have ht := F.right_eq
  constructor <;> apply Fin.ext <;> dsimp only at hfla hfub <;> omega

include hdim in
theorem degree_eq : PureBoundaryGraphIntegral.Degree (n := n) (l := F.l) (u := F.u) = r := by
  have hc : shapeM F.l F.u = 2 := (Fintype.card_coe _).trans F.card_eq
  have hs := boundary_card_sum (l := F.l) (u := F.u)
  rw [hc] at hs
  dsimp [PureBoundaryGraphIntegral.Degree, GraphForms.dimension] at hdim ⊢
  omega

def coordinates : PureBoundaryClusterForms.Face n (boundaryClusterBlock F.l F.u) F.a F.b ≃L[ℝ] Coord r :=
  (PureBoundaryGraphIntegral.faceCoordinates F.ordered F.a F.b F.left_mem F.right_mem F.endpoints.ne F.card_eq).trans
    (ForestGlobalGraphStokes.coordinateCast (degree_eq hdim F))

def region : Set (Coord r) := (coordinates hdim F).symm ⁻¹'
  PureBoundaryGraphDomain.nativeDomain (n := n) (l := F.l) (u := F.u) F.a F.b

def cutoff (ρ : OriginalPartitionCancellation.Ambient n m → ℝ) (y : Coord r) : ℝ :=
  ρ (CompactDRCoordinates.realCoordinates (n+1) m
    (PureBoundaryFaceDR.ambient F.l F.u F.a F.b ((coordinates hdim F).symm y)))

def form (es : Fin r → GraphForms.Edge n m) : TopForm r := fun y ↦
  (PureBoundaryClusterForms.faceGraphForm (boundaryClusterBlock F.l F.u) F.a F.b es
    ((coordinates hdim F).symm y)).compContinuousLinearMap (coordinates hdim F).symm.toContinuousLinearMap

theorem measurableSet_region : MeasurableSet (region hdim F) := by
  unfold region
  rw [PureBoundaryGraphDomain.nativeDomain_eq_preimage F.ordered F.left_mem F.right_mem
    F.endpoints F.card_eq F.left_eq F.right_eq]
  exact ((GraphForms.isOpen_admissibleSet _ _).preimage
    ((PureBoundaryGraphQuotient.twoPointCoordinates F.ordered F.a F.b F.left_mem F.right_mem
      F.endpoints.ne F.card_eq).continuous.comp (coordinates hdim F).symm.continuous)).measurableSet

theorem sum_cutoff {J : Type*} [Fintype J] (ρ : OriginalPartitionCancellation.Partition J n m)
    (y : Coord r) (hy : y ∈ region hdim F) : (∑ j, cutoff hdim F (ρ j) y) = 1 := by
  obtain ⟨D,hd⟩ := hy
  change (PureBoundaryClusterForms.dataCoarse D, PureBoundaryClusterForms.dataShape D) =
    (coordinates hdim F).symm y at hd
  simp_rw [cutoff, ← hd, PureBoundaryFaceDR.ambient_data]
  simpa only [finsum_eq_sum_of_fintype, CompactDRCoordinates.embedding, compactProjectDR] using
    ρ.sum_eq_one (Set.mem_range_self D.boundaryPoint)

variable (x : Compactification (0 : Fin (n+1)) m) (o : Orbit 0 x)
  (ho : kind 0 x o = .pureBoundary)
  (hl : PureForestSimpleCluster.lower x o = F.l)
  (hu : PureForestSimpleCluster.upper x o = F.u)

include ho hl hu in
theorem oriented_contribution_eq
    (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)
    (hρ : tsupport (CompactDRAmbientPartition.cutoff 0 ρ) ⊆ (ForestChartOrientation.smallChart 0 x).target)
    (es : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (es j).target ≠ Sum.inl (es j).source)
    (κ : ForestOrthantRealization.Ambient 0 x → ℝ)
    (hmatch : ForestRadialFaceLocalization.LocalizationAgreement x ρ es hloop κ)
    (ε : ℝ) (hε : ∀ y ∈ ForestGlobalGraphStokes.positiveRegion hdim x,
      ε * jacobian (ForestGlobalGraphStokes.chart hdim x) y =
        |jacobian (ForestGlobalGraphStokes.chart hdim x) y|) :
    ε * contribution hdim x (ForestGlobalGraphStokes.localForm hdim x ρ es hloop κ) o =
      (-1 : ℝ)^F.a.val * ∫ y in region hdim F, cutoff hdim F ρ y * density (form hdim F es) y := by
  rcases F with ⟨l,u,a,b,hlu,ha,hb,hab,hal,hbu,hcard⟩
  dsimp only at hl hu
  subst l u
  have h := MainPureFixedChartIntegral.oriented_contribution_eq_full_weighted_integral
    hdim x o a b ho hal hbu hab hcard ρ hρ es hloop κ hmatch ε hε
  have he : (fun j ↦ (⟨(ForestPositiveGraphForms.forestEdge 0 (es j) (hloop j)).source,
      (ForestPositiveGraphForms.forestEdge 0 (es j) (hloop j)).target⟩ : GraphForms.Edge n m)) = es := by
    funext j
    simp [ForestPositiveGraphForms.forestEdge, Equiv.swap_self]
  let F' : FaceData m := ⟨_,_,a,b,hlu,ha,hb,hab,hal,hbu,hcard⟩
  change ε * contribution hdim x (ForestGlobalGraphStokes.localForm hdim x ρ es hloop κ) o =
    (-1 : ℝ)^a.val * ∫ y in region hdim F', cutoff hdim F' ρ y * density
      (form hdim F' (fun j ↦ ⟨(ForestPositiveGraphForms.forestEdge 0 (es j) (hloop j)).source,
        (ForestPositiveGraphForms.forestEdge 0 (es j) (hloop j)).target⟩)) y at h
  rw [he] at h
  exact h

include ho hl hu in
theorem integrableOn_weighted_density
    (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)
    (hρ : tsupport (CompactDRAmbientPartition.cutoff 0 ρ) ⊆ (ForestChartOrientation.smallChart 0 x).target)
    (es : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (es j).target ≠ Sum.inl (es j).source)
    (κ : ForestOrthantRealization.Ambient 0 x → ℝ)
    (hmatch : ForestRadialFaceLocalization.LocalizationAgreement x ρ es hloop κ)
    (hcont : Continuous (ForestGlobalGraphStokes.localForm hdim x ρ es hloop κ))
    (hcompact : HasCompactSupport (ForestGlobalGraphStokes.localForm hdim x ρ es hloop κ))
    (ε : ℝ) (hε : ∀ y ∈ ForestGlobalGraphStokes.positiveRegion hdim x,
      ε * jacobian (ForestGlobalGraphStokes.chart hdim x) y =
        |jacobian (ForestGlobalGraphStokes.chart hdim x) y|) :
    IntegrableOn (fun y ↦ cutoff hdim F ρ y * density (form hdim F es) y) (region hdim F) := by
  rcases F with ⟨l,u,a,b,hlu,ha,hb,hab,hal,hbu,hcard⟩
  dsimp only at hl hu
  subst l u
  have h := MainPureFixedChartIntegrability.integrableOn_full_weighted_density
    hdim x o a b ho hal hbu hab hcard ρ hρ es hloop κ hmatch hcont hcompact ε hε
  have he : (fun j ↦ (⟨(ForestPositiveGraphForms.forestEdge 0 (es j) (hloop j)).source,
      (ForestPositiveGraphForms.forestEdge 0 (es j) (hloop j)).target⟩ : GraphForms.Edge n m)) = es := by
    funext j
    simp [ForestPositiveGraphForms.forestEdge, Equiv.swap_self]
  let F' : FaceData m := ⟨_,_,a,b,hlu,ha,hb,hab,hal,hbu,hcard⟩
  change IntegrableOn (fun y ↦ cutoff hdim F' ρ y * density
      (form hdim F' (fun j ↦ ⟨(ForestPositiveGraphForms.forestEdge 0 (es j) (hloop j)).source,
        (ForestPositiveGraphForms.forestEdge 0 (es j) (hloop j)).target⟩)) y) (region hdim F') at h
  rw [he] at h
  exact h

end EnvelopingIsomorphism.Deformation.MainPurePhysicalFace
