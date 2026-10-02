import EnvelopingIsomorphism.Deformation.Kontsevich.SimpleFaceNativeAtlas

/-! Exact integer-lift counting for the paired face. The half-open angular
fundamental region has one representative per circle point; the closed region
used by integration differs only on a null seam. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestAngleFundamentalDomain
open Configuration InteriorGraphFaceCoordinates InteriorFacePartitionReassembly
open InteriorFiberAngleSplit SimpleProductPhaseIdentification Set MeasureTheory
open scoped Classical
variable {n m : ℕ} {i a b : Fin n} {S : Finset (Fin n)}

def FaceRegionIco (i a b : Fin n) (S : Finset (Fin n)) (m : ℕ) :
    Set (RealProductCoordinates i a b S m) :=
  (Ico (0 : ℝ) (2 * Real.pi) ×ˢ shapeConfiguration (shapeN a b S)) ×ˢ
    GeometricWeights.realDomain (coarseN i a S) m

theorem measurableSet_faceRegionIco : MeasurableSet (FaceRegionIco i a b S m) :=
  (measurableSet_Ico.prod (isOpen_shapeConfiguration _).measurableSet).prod
    (GeometricWeights.measurableSet_realDomain _ _)

/-- The integration convention includes both endpoints, but the second copy
of the angular seam has zero product volume. -/
theorem faceRegionIco_ae_eq_faceRegion {N : ℕ} {i a b : Fin (N + 1)} {S : Finset (Fin (N + 1))} :
    FaceRegionIco i a b S m =ᵐ[volume] FaceRegion i a b S m := by
  change (Ico (0 : ℝ) (2 * Real.pi) ×ˢ shapeConfiguration (shapeN a b S)) ×ˢ
      GeometricWeights.realDomain (coarseN i a S) m =ᵐ[volume]
    (Icc (0 : ℝ) (2 * Real.pi) ×ˢ shapeConfiguration (shapeN a b S)) ×ˢ
      GeometricWeights.realDomain (coarseN i a S) m
  rw [Measure.volume_eq_prod]
  apply Measure.set_prod_ae_eq _ Filter.EventuallyEq.rfl
  rw [Measure.volume_eq_prod]
  exact Measure.set_prod_ae_eq Ico_ae_eq_Icc Filter.EventuallyEq.rfl

theorem integral_faceRegionIco_eq {N : ℕ} {i a b : Fin (N + 1)} {S : Finset (Fin (N + 1))}
    (f : RealProductCoordinates i a b S m → ℝ) :
    (∫ p in FaceRegionIco i a b S m, f p) = ∫ p in FaceRegion i a b S m, f p :=
  setIntegral_congr_set faceRegionIco_ae_eq_faceRegion

theorem existsUnique_int_lift (p : ProductCoordinates i a b S m) :
    ∃! k : ℤ, (shift k p).1.1 ∈ Ico 0 (2 * Real.pi) := by
  simpa only [shift, zero_add, zsmul_eq_mul] using
    existsUnique_add_zsmul_mem_Ico Real.two_pi_pos p.1.1 0

/-- The actual compactification encoder is injective on the half-open phase
region, with no multiplicity from choosing different angle branches. -/
theorem eq_of_boundaryPoint_eq_of_angle_mem
    (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hanchor : i ∈ S → a = i)
    (p q : ProductCoordinates i a b S m)
    (hp : (toAngular p).toFree.OpenConditions) (hq : (toAngular q).toFree.OpenConditions)
    (hap : p.1.1 ∈ Ico 0 (2 * Real.pi)) (haq : q.1.1 ∈ Ico 0 (2 * Real.pi))
    (h : (InteriorFaceDRCoordinates.datum ha hb hanchor p hp).toInteriorCollisionData.boundaryPoint =
      (InteriorFaceDRCoordinates.datum ha hb hanchor q hq).toInteriorCollisionData.boundaryPoint) : p = q := by
  have hf := free_eq_of_boundaryPoint_eq ha hb hba hanchor p q hp hq h
  have he : Circle.exp p.1.1 = Circle.exp q.1.1 :=
    congrArg (fun z : ClusterFreeCoordinates i a b S m ↦ z.2.2.2.1) hf
  have hangle := Circle.exp_injOn_Ico (by simp : 2 * Real.pi - 0 ≤ 2 * Real.pi) hap haq he
  obtain ⟨k, hk⟩ := eq_shift_of_free_eq p q hf
  have hθ := congrArg (fun z : ProductCoordinates i a b S m ↦ z.1.1) hk
  change p.1.1 = q.1.1 + (k : ℝ) * (2 * Real.pi) at hθ
  have hkzero : k = 0 := by
    have hmul : (k : ℝ) * (2 * Real.pi) = 0 := by rw [hangle] at hθ; linarith
    exact_mod_cast (mul_eq_zero.mp hmul).resolve_right Real.two_pi_pos.ne'
  simpa only [hkzero, shift, Int.cast_zero, zero_mul, add_zero, Prod.mk.eta] using hk

open PairedForestSmoothProduct PairedForestProductChart BoxStokes
variable {N r : ℕ} (hdim : GraphForms.dimension N m = r + 1)
  (x : Compactification (0 : Fin (N + 1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (ho : ForestRadialFaceClassification.kind 0 x o = .paired) (z : Source hdim x o)

def liftPiece (s : Set (Coord r)) (k : ℤ) : Set (Coord r) :=
  s ∩ {w | (localChart hdim x o ho z w).1.1 + (k : ℝ) * (2 * Real.pi) ∈ Ico 0 (2 * Real.pi)}

theorem measurableSet_liftPiece (s : Set (Coord r)) (hs : MeasurableSet s)
    (hsub : s ⊆ (localChart hdim x o ho z).source) (k : ℤ) :
    MeasurableSet (liftPiece hdim x o ho z s k) := by
  let A : Coord r → ℝ := (localChart hdim x o ho z).source.piecewise
    (fun w ↦ (localChart hdim x o ho z w).1.1) (fun _ ↦ 0)
  have hA : Measurable A :=
    (localChart hdim x o ho z).continuousOn.fst.fst.measurable_piecewise
      continuous_const.continuousOn (localChart hdim x o ho z).open_source.measurableSet
  have he : liftPiece hdim x o ho z s k = s ∩
      (fun w ↦ A w + (k : ℝ) * (2 * Real.pi)) ⁻¹' Ico 0 (2 * Real.pi) := by
    ext w
    by_cases hw : w ∈ s
    · simp only [liftPiece, mem_inter_iff, mem_setOf_eq, hw, true_and, mem_preimage]
      rw [show A w = (localChart hdim x o ho z w).1.1 from by simp only [A, piecewise_eq_of_mem _ _ _ (hsub hw)]]
    · simp only [liftPiece, mem_inter_iff, hw, false_and]
  rw [he]
  exact hs.inter ((hA.add_const _ ) measurableSet_Ico)

theorem pairwiseDisjoint_liftPiece (s : Set (Coord r)) :
    Pairwise (fun k l : ℤ ↦ Disjoint (liftPiece hdim x o ho z s k) (liftPiece hdim x o ho z s l)) := by
  intro k l hkl
  apply disjoint_left.mpr
  intro w hwk hwl
  obtain ⟨j, hj, hu⟩ := existsUnique_int_lift (localChart hdim x o ho z w)
  exact hkl ((hu k hwk.2).trans (hu l hwl.2).symm)

theorem iUnion_liftPiece (s : Set (Coord r)) :
    (⋃ k : ℤ, liftPiece hdim x o ho z s k) = s := by
  apply subset_antisymm
  · exact iUnion_subset fun _ ↦ inter_subset_left
  · intro w hw
    obtain ⟨k, hk, _⟩ := existsUnique_int_lift (localChart hdim x o ho z w)
    exact mem_iUnion.mpr ⟨k, hw, hk⟩

/-- Integer-lift splitting is an exact countable integral identity obtained
from a proved measurable disjoint partition, rather than an assumed degree. -/
theorem hasSum_integral_liftPiece (s : Set (Coord r)) (hs : MeasurableSet s)
    (hsub : s ⊆ (localChart hdim x o ho z).source) (f : Coord r → ℝ) (hf : IntegrableOn f s) :
    HasSum (fun k : ℤ ↦ ∫ w in liftPiece hdim x o ho z s k, f w) (∫ w in s, f w) := by
  have h := hasSum_integral_iUnion (measurableSet_liftPiece hdim x o ho z s hs hsub)
    (pairwiseDisjoint_liftPiece hdim x o ho z s)
    (show IntegrableOn f (⋃ k : ℤ, liftPiece hdim x o ho z s k) from
      (iUnion_liftPiece hdim x o ho z s).symm ▸ hf)
  simpa only [iUnion_liftPiece] using h

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestAngleFundamentalDomain
