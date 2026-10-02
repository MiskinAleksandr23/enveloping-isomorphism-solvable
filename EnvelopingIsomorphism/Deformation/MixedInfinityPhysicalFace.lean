import EnvelopingIsomorphism.Deformation.MainInfinityFixedChartIntegrability
import EnvelopingIsomorphism.Deformation.MainPurePhysicalFace

/-! Shared physical coordinates for each surviving mixed infinity face. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace EnvelopingIsomorphism.Deformation.MixedInfinityPhysicalFace
open Kontsevich Configuration ForestRadialFaceClassification
open Set MeasureTheory BoxStokes OrientedFormChangeVariables
open scoped Classical

structure FaceData where
  l : Fin 3
  u : Fin 3
  a : Fin 2
  ordered : l ≤ u
  left_mem : a ∈ boundaryClusterBlock l u
  card_eq : (boundaryClusterBlock l u).card = 1
  q : Fin 2
  outside : q ∉ boundaryClusterBlock l u

namespace FaceData
variable (F : FaceData)
theorem nonempty : (boundaryClusterBlock F.l F.u).Nonempty := ⟨F.a,F.left_mem⟩
theorem all_inside : ∀ j : Fin 2, j ≠ F.q → j ∈ boundaryClusterBlock F.l F.u :=
  InfinityBoundaryGraphCoordinates.onlyOutside_of_card F.outside F.card_eq
theorem block_endpoints_eq {l u : Fin 3}
    (he : boundaryClusterBlock l u = boundaryClusterBlock F.l F.u) : l = F.l ∧ u = F.u := by
  have h : ∀ l u L U : Fin 3, (boundaryClusterBlock L U).card = 1 →
      boundaryClusterBlock l u = boundaryClusterBlock L U → l = L ∧ u = U := by decide
  exact h l u F.l F.u F.card_eq he
end FaceData

variable {n r : ℕ} (hdim : GraphForms.dimension n 2 = r+1) (F : FaceData)

include hdim in
theorem degree_eq : InfinityBoundaryGraphIntegral.Degree (0 : Fin (n+1)) F.l F.u = r := by
  have hc : InfinityBoundaryGraphFactorization.shapeM F.l F.u = 1 :=
    (Fintype.card_coe _).trans F.card_eq
  simp only [InfinityBoundaryGraphIntegral.Degree, GraphForms.dimension,
    InfinityBoundaryGraphFactorization.shapeN,card_boundaryAnchoredInfinityFreeInterior,hc] at *
  omega

def coordinates : BoundaryAnchoredInfinityFreeCoordinates.FaceCoordinates (0 : Fin (n+1)) 2 F.q ≃L[ℝ] Coord r :=
  (InfinityBoundaryGraphIntegral.faceCoordinates F.outside F.all_inside).trans
    (ForestGlobalGraphStokes.coordinateCast (degree_eq hdim F))

def region : Set (Coord r) := {y | (BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding
  ((coordinates hdim F).symm y)).OpenConditions F.l F.u}

def point (y : region hdim F) : Compactification (0 : Fin (n+1)) 2 :=
  (BoundaryAnchoredInfinityFreeCoordinates.faceDomain ((coordinates hdim F).symm y.val) y.property).toDomain.insertion

def cutoff (ρ : OriginalPartitionCancellation.Ambient n 2 → ℝ) (y : Coord r) : ℝ :=
  if hy : y ∈ region hdim F then CompactDRAmbientPartition.cutoff 0 ρ (point hdim F ⟨y,hy⟩) else 0

def form (es : Fin r → GraphForms.Edge n 2) : TopForm r := fun y ↦
  ((InfinityBoundaryGraphFactorization.graphForm (l := F.l) (u := F.u)
    (fun j ↦ ((es j).source,(es j).target))
    (BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding ((coordinates hdim F).symm y))).compContinuousLinearMap
      BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding).compContinuousLinearMap
        (coordinates hdim F).symm.toContinuousLinearMap

theorem measurableSet_region : MeasurableSet (region hdim F) :=
  ((BoundaryAnchoredInfinityFreeCoordinates.isOpen_openConditions (a := (0 : Fin (n+1))) (o := F.q)
    F.l F.u).preimage (BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding.continuous.comp
      (coordinates hdim F).symm.continuous)).measurableSet

theorem sum_cutoff {J : Type*} [Fintype J] (ρ : OriginalPartitionCancellation.Partition J n 2)
    (y : Coord r) (hy : y ∈ region hdim F) : (∑ j, cutoff hdim F (ρ j) y) = 1 := by
  simp only [cutoff,dif_pos hy,CompactDRAmbientPartition.cutoff]
  simpa only [finsum_eq_sum_of_fintype, CompactDRCoordinates.embedding, compactProjectDR] using
    ρ.sum_eq_one (Set.mem_range_self (point hdim F ⟨y,hy⟩))

def nativeEdges (es : Fin r → GraphForms.Edge n 2) :
    Fin (InfinityBoundaryGraphIntegral.Degree (0 : Fin (n+1)) F.l F.u) →
      InfinityBoundaryGraphFactorization.Edge (n+1) 2 :=
  fun t ↦ let e := es (finCongr (degree_eq hdim F) t); (e.source,e.target)

theorem density_eq_native (es : Fin r → GraphForms.Edge n 2) (y : Coord r) :
    density (form hdim F es) y =
      BoxStokes.facePullback (InfinityBoundaryGraphIntegral.radialForm F.outside F.all_inside
        (nativeEdges hdim F es)) 0 0
        ((ForestGlobalGraphStokes.coordinateCast (degree_eq hdim F)).symm y) (standardBasis _) := by
  have hd := degree_eq hdim F
  subst r
  rw [InfinityBoundaryGraphIntegral.facePullback_eq_native]
  rfl

theorem integral_eq_neg_outwardIntegral (es : Fin r → GraphForms.Edge n 2) :
    (∫ y in region hdim F, density (form hdim F es) y) =
      -InfinityBoundaryGraphIntegral.outwardIntegral F.outside F.all_inside (nativeEdges hdim F es) := by
  have hd := degree_eq hdim F
  subst r
  simp only [InfinityBoundaryGraphIntegral.outwardIntegral,neg_neg]
  apply setIntegral_congr_fun (measurableSet_region hdim F)
  intro y hy
  exact density_eq_native hdim F es y

variable (x : Compactification (0 : Fin (n+1)) 2) (o : Orbit 0 x)
  (ho : kind 0 x o = .infinity)
  (hl : InfinityForestSimpleCluster.lower x o = F.l)
  (hu : InfinityForestSimpleCluster.upper x o = F.u)

include ho hl hu in
theorem oriented_contribution_eq
    (ρ : OriginalPartitionCancellation.Ambient n 2 → ℝ)
    (hρ : tsupport (CompactDRAmbientPartition.cutoff 0 ρ) ⊆ (ForestChartOrientation.smallChart 0 x).target)
    (es : Fin r → GraphForms.Edge n 2) (hloop : ∀ j, (es j).target ≠ Sum.inl (es j).source)
    (κ : ForestOrthantRealization.Ambient 0 x → ℝ)
    (hmatch : ForestRadialFaceLocalization.LocalizationAgreement x ρ es hloop κ)
    (ε : ℝ) (hε : ∀ y ∈ ForestGlobalGraphStokes.positiveRegion hdim x,
      ε * jacobian (ForestGlobalGraphStokes.chart hdim x) y = |jacobian (ForestGlobalGraphStokes.chart hdim x) y|) :
    ε * contribution hdim x (ForestGlobalGraphStokes.localForm hdim x ρ es hloop κ) o =
      (BoundaryAnchoredInfinityData.referenceSign F.l F.q * (-1 : ℝ)^F.q.val) *
        ∫ y in region hdim F, cutoff hdim F ρ y * density (form hdim F es) y := by
  rcases F with ⟨l,u,a,hlu,ha,hcard,q,hq⟩
  dsimp only at hl hu
  subst l u
  have h := MainInfinityFixedChartIntegral.oriented_contribution_eq_full_weighted_integral
    hdim x o q ho hq ⟨a,ha⟩ (InfinityBoundaryGraphCoordinates.onlyOutside_of_card hq hcard)
    ρ hρ es hloop κ hmatch ε hε
  let F' : FaceData := ⟨_,_,a,hlu,ha,hcard,q,hq⟩
  have he : (fun j ↦ ((ForestPositiveGraphForms.forestEdge 0 (es j) (hloop j)).source,
      (ForestPositiveGraphForms.forestEdge 0 (es j) (hloop j)).target)) =
      (fun j ↦ ((es j).source,(es j).target)) := by
    funext j
    simp [ForestPositiveGraphForms.forestEdge,Equiv.swap_self]
  have hf : InfinityForestFaceChangeVariables.simpleForm hdim x o q ho hq ⟨a,ha⟩
      (InfinityBoundaryGraphCoordinates.onlyOutside_of_card hq hcard)
      (fun j ↦ ForestPositiveGraphForms.forestEdge 0 (es j) (hloop j)) = form hdim F' es := by
    funext y
    dsimp only [InfinityForestFaceChangeVariables.simpleForm,InfinityForestFaceChangeVariables.simpleFaceForm,form]
    rw [he]
    rfl
  rw [hf] at h
  exact h

include ho hl hu in
theorem integrableOn_weighted_density
    (ρ : OriginalPartitionCancellation.Ambient n 2 → ℝ)
    (hρ : tsupport (CompactDRAmbientPartition.cutoff 0 ρ) ⊆ (ForestChartOrientation.smallChart 0 x).target)
    (es : Fin r → GraphForms.Edge n 2) (hloop : ∀ j, (es j).target ≠ Sum.inl (es j).source)
    (κ : ForestOrthantRealization.Ambient 0 x → ℝ)
    (hmatch : ForestRadialFaceLocalization.LocalizationAgreement x ρ es hloop κ)
    (hcont : Continuous (ForestGlobalGraphStokes.localForm hdim x ρ es hloop κ))
    (hcompact : HasCompactSupport (ForestGlobalGraphStokes.localForm hdim x ρ es hloop κ))
    (ε : ℝ) (hε : ∀ y ∈ ForestGlobalGraphStokes.positiveRegion hdim x,
      ε * jacobian (ForestGlobalGraphStokes.chart hdim x) y = |jacobian (ForestGlobalGraphStokes.chart hdim x) y|) :
    IntegrableOn (fun y ↦ cutoff hdim F ρ y * density (form hdim F es) y) (region hdim F) := by
  rcases F with ⟨l,u,a,hlu,ha,hcard,q,hq⟩
  dsimp only at hl hu
  subst l u
  have h := MainInfinityFixedChartIntegrability.integrableOn_full_weighted_density
    hdim x o q ho hq ⟨a,ha⟩ (InfinityBoundaryGraphCoordinates.onlyOutside_of_card hq hcard)
    ρ hρ es hloop κ hmatch hcont hcompact ε hε
  let F' : FaceData := ⟨_,_,a,hlu,ha,hcard,q,hq⟩
  have he : (fun j ↦ ((ForestPositiveGraphForms.forestEdge 0 (es j) (hloop j)).source,
      (ForestPositiveGraphForms.forestEdge 0 (es j) (hloop j)).target)) =
      (fun j ↦ ((es j).source,(es j).target)) := by
    funext j
    simp [ForestPositiveGraphForms.forestEdge,Equiv.swap_self]
  have hf : InfinityForestFaceChangeVariables.simpleForm hdim x o q ho hq ⟨a,ha⟩
      (InfinityBoundaryGraphCoordinates.onlyOutside_of_card hq hcard)
      (fun j ↦ ForestPositiveGraphForms.forestEdge 0 (es j) (hloop j)) = form hdim F' es := by
    funext y
    dsimp only [InfinityForestFaceChangeVariables.simpleForm,InfinityForestFaceChangeVariables.simpleFaceForm,form]
    rw [he]
    rfl
  rw [hf] at h
  exact h

end EnvelopingIsomorphism.Deformation.MixedInfinityPhysicalFace
