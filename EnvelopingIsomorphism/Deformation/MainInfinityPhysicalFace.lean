import EnvelopingIsomorphism.Deformation.MainInfinityFixedChartIntegrability
import EnvelopingIsomorphism.Deformation.MainPurePhysicalFace

/-! Shared physical coordinates for each surviving main infinity face. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.MainInfinityPhysicalFace
open Kontsevich Configuration ForestRadialFaceClassification
open Set MeasureTheory BoxStokes OrientedFormChangeVariables
open scoped Classical

structure FaceData extends MainPurePhysicalFace.FaceData 3 where
  q : Fin 3
  outside : q ∉ boundaryClusterBlock l u

namespace FaceData
variable (F : FaceData)
theorem nonempty : (boundaryClusterBlock F.l F.u).Nonempty := ⟨F.a,F.left_mem⟩
theorem all_inside : ∀ j : Fin 3, j ≠ F.q → j ∈ boundaryClusterBlock F.l F.u :=
  InfinityBoundaryGraphCoordinates.onlyOutside_of_card F.outside F.card_eq
end FaceData

variable {n r : ℕ} (hdim : GraphForms.dimension n 3 = r+1) (F : FaceData)

include hdim in
theorem degree_eq : InfinityBoundaryGraphIntegral.Degree (0 : Fin (n+1)) F.l F.u = r := by
  have hc : InfinityBoundaryGraphFactorization.shapeM F.l F.u = 2 :=
    (Fintype.card_coe _).trans F.card_eq
  simp only [InfinityBoundaryGraphIntegral.Degree, GraphForms.dimension,
    InfinityBoundaryGraphFactorization.shapeN,card_boundaryAnchoredInfinityFreeInterior,hc] at *
  omega

def coordinates : BoundaryAnchoredInfinityFreeCoordinates.FaceCoordinates (0 : Fin (n+1)) 3 F.q ≃L[ℝ] Coord r :=
  (InfinityBoundaryGraphIntegral.faceCoordinates F.outside F.all_inside).trans
    (ForestGlobalGraphStokes.coordinateCast (degree_eq hdim F))

def region : Set (Coord r) := {y | (BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding
  ((coordinates hdim F).symm y)).OpenConditions F.l F.u}

def point (y : region hdim F) : Compactification (0 : Fin (n+1)) 3 :=
  (BoundaryAnchoredInfinityFreeCoordinates.faceDomain ((coordinates hdim F).symm y.val) y.property).toDomain.insertion

def cutoff (ρ : OriginalPartitionCancellation.Ambient n 3 → ℝ) (y : Coord r) : ℝ :=
  if hy : y ∈ region hdim F then CompactDRAmbientPartition.cutoff 0 ρ (point hdim F ⟨y,hy⟩) else 0

def form (es : Fin r → GraphForms.Edge n 3) : TopForm r := fun y ↦
  ((InfinityBoundaryGraphFactorization.graphForm (l := F.l) (u := F.u)
    (fun j ↦ ((es j).source,(es j).target))
    (BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding ((coordinates hdim F).symm y))).compContinuousLinearMap
      BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding).compContinuousLinearMap
        (coordinates hdim F).symm.toContinuousLinearMap

theorem measurableSet_region : MeasurableSet (region hdim F) :=
  ((BoundaryAnchoredInfinityFreeCoordinates.isOpen_openConditions (a := (0 : Fin (n+1))) (o := F.q)
    F.l F.u).preimage (BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding.continuous.comp
      (coordinates hdim F).symm.continuous)).measurableSet

theorem sum_cutoff {J : Type*} [Fintype J] (ρ : OriginalPartitionCancellation.Partition J n 3)
    (y : Coord r) (hy : y ∈ region hdim F) : (∑ j, cutoff hdim F (ρ j) y) = 1 := by
  simp only [cutoff,dif_pos hy,CompactDRAmbientPartition.cutoff]
  simpa only [finsum_eq_sum_of_fintype, CompactDRCoordinates.embedding, compactProjectDR] using
    ρ.sum_eq_one (Set.mem_range_self (point hdim F ⟨y,hy⟩))

def nativeEdges (es : Fin r → GraphForms.Edge n 3) :
    Fin (InfinityBoundaryGraphIntegral.Degree (0 : Fin (n+1)) F.l F.u) →
      InfinityBoundaryGraphFactorization.Edge (n+1) 3 :=
  fun t ↦ let e := es (finCongr (degree_eq hdim F) t); (e.source,e.target)

theorem density_eq_native (es : Fin r → GraphForms.Edge n 3) (y : Coord r) :
    density (form hdim F es) y =
      BoxStokes.facePullback (InfinityBoundaryGraphIntegral.radialForm F.outside F.all_inside
        (nativeEdges hdim F es)) 0 0
        ((ForestGlobalGraphStokes.coordinateCast (degree_eq hdim F)).symm y) (standardBasis _) := by
  have hd := degree_eq hdim F
  subst r
  rw [InfinityBoundaryGraphIntegral.facePullback_eq_native]
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 1600000 in
theorem integral_eq_neg_outwardIntegral (es : Fin r → GraphForms.Edge n 3) :
    (∫ y in region hdim F, density (form hdim F es) y) =
      -InfinityBoundaryGraphIntegral.outwardIntegral F.outside F.all_inside (nativeEdges hdim F es) := by
  let e := (ForestGlobalGraphStokes.coordinateCast (degree_eq hdim F)).symm
  have hm : MeasurePreserving e volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : Fin _ => ℝ) (finCongr (degree_eq hdim F).symm)
  have h := hm.setIntegral_preimage_emb e.toHomeomorph.measurableEmbedding
    (fun y ↦ BoxStokes.facePullback (InfinityBoundaryGraphIntegral.radialForm F.outside F.all_inside
      (nativeEdges hdim F es)) 0 0 y (standardBasis _))
    (InfinityBoundaryGraphIntegral.nativeDomain (a := (0 : Fin (n+1))) F.outside F.all_inside)
  rw [show e ⁻¹' InfinityBoundaryGraphIntegral.nativeDomain F.outside F.all_inside = region hdim F from rfl] at h
  simp only [InfinityBoundaryGraphIntegral.outwardIntegral,neg_neg]
  rw [← h]
  apply setIntegral_congr_fun (measurableSet_region hdim F)
  intro y hy
  exact density_eq_native hdim F es y

variable (x : Compactification (0 : Fin (n+1)) 3) (o : Orbit 0 x)
  (ho : kind 0 x o = .infinity)
  (hl : InfinityForestSimpleCluster.lower x o = F.l)
  (hu : InfinityForestSimpleCluster.upper x o = F.u)

include ho hl hu in
theorem oriented_contribution_eq
    (ρ : OriginalPartitionCancellation.Ambient n 3 → ℝ)
    (hρ : tsupport (CompactDRAmbientPartition.cutoff 0 ρ) ⊆ (ForestChartOrientation.smallChart 0 x).target)
    (es : Fin r → GraphForms.Edge n 3) (hloop : ∀ j, (es j).target ≠ Sum.inl (es j).source)
    (κ : ForestOrthantRealization.Ambient 0 x → ℝ)
    (hmatch : ForestRadialFaceLocalization.LocalizationAgreement x ρ es hloop κ)
    (ε : ℝ) (hε : ∀ y ∈ ForestGlobalGraphStokes.positiveRegion hdim x,
      ε * jacobian (ForestGlobalGraphStokes.chart hdim x) y = |jacobian (ForestGlobalGraphStokes.chart hdim x) y|) :
    ε * contribution hdim x (ForestGlobalGraphStokes.localForm hdim x ρ es hloop κ) o =
      (BoundaryAnchoredInfinityData.referenceSign F.l F.q * (-1 : ℝ)^F.q.val) *
        ∫ y in region hdim F, cutoff hdim F ρ y * density (form hdim F es) y := by
  rcases F with ⟨⟨l,u,a,b,hlu,ha,hb,hab,hal,hbu,hcard⟩,q,hq⟩
  dsimp only at hl hu
  subst l u
  have h := MainInfinityFixedChartIntegral.oriented_contribution_eq_full_weighted_integral
    hdim x o q ho hq ⟨a,ha⟩ (InfinityBoundaryGraphCoordinates.onlyOutside_of_card hq hcard)
    ρ hρ es hloop κ hmatch ε hε
  let F' : FaceData := ⟨⟨_,_,a,b,hlu,ha,hb,hab,hal,hbu,hcard⟩,q,hq⟩
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
    (ρ : OriginalPartitionCancellation.Ambient n 3 → ℝ)
    (hρ : tsupport (CompactDRAmbientPartition.cutoff 0 ρ) ⊆ (ForestChartOrientation.smallChart 0 x).target)
    (es : Fin r → GraphForms.Edge n 3) (hloop : ∀ j, (es j).target ≠ Sum.inl (es j).source)
    (κ : ForestOrthantRealization.Ambient 0 x → ℝ)
    (hmatch : ForestRadialFaceLocalization.LocalizationAgreement x ρ es hloop κ)
    (hcont : Continuous (ForestGlobalGraphStokes.localForm hdim x ρ es hloop κ))
    (hcompact : HasCompactSupport (ForestGlobalGraphStokes.localForm hdim x ρ es hloop κ))
    (ε : ℝ) (hε : ∀ y ∈ ForestGlobalGraphStokes.positiveRegion hdim x,
      ε * jacobian (ForestGlobalGraphStokes.chart hdim x) y = |jacobian (ForestGlobalGraphStokes.chart hdim x) y|) :
    IntegrableOn (fun y ↦ cutoff hdim F ρ y * density (form hdim F es) y) (region hdim F) := by
  rcases F with ⟨⟨l,u,a,b,hlu,ha,hb,hab,hal,hbu,hcard⟩,q,hq⟩
  dsimp only at hl hu
  subst l u
  have h := MainInfinityFixedChartIntegrability.integrableOn_full_weighted_density
    hdim x o q ho hq ⟨a,ha⟩ (InfinityBoundaryGraphCoordinates.onlyOutside_of_card hq hcard)
    ρ hρ es hloop κ hmatch hcont hcompact ε hε
  let F' : FaceData := ⟨⟨_,_,a,b,hlu,ha,hb,hab,hal,hbu,hcard⟩,q,hq⟩
  let F' : FaceData := ⟨⟨_,_,a,b,hlu,ha,hb,hab,hal,hbu,hcard⟩,q,hq⟩
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

end EnvelopingIsomorphism.Deformation.MainInfinityPhysicalFace
