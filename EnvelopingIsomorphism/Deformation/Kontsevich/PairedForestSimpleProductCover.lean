import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestCanonicalProductCoverage
import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointFacePartitionReassembly

/-! A countable disjoint measurable cover of a full simple product face by
actual native IFT charts, with canonical mark transport and integral angular
translations. Native centers may vary over the simple face. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestSimpleProductCover
open Configuration BoxStokes ForestRadialFaceClassification PairedForestSimpleCluster
open PairedForestSmoothProduct PairedForestProductChart PairedForestCanonicalProductCoverage
open InteriorGraphFaceCoordinates InteriorFacePartitionReassembly MeasureTheory Set
open scoped Classical Topology
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  {S : Finset (Fin (n+1))} {a b : Fin (n+1)}
  (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hanchor : (0 : Fin (n+1)) ∈ S → a = 0)
  (haMark : a = PairedForestCanonicalMarks.canonicalAnchor S)
  (hbMark : b = PairedForestCanonicalMarks.canonicalReference S)

abbrev RealSpace := RealProductCoordinates (0 : Fin (n+1)) a b S m
abbrev Face := FaceRegion (0 : Fin (n+1)) a b S m

/-- Every selected chart retains its original native source and constructed
map; only mark identification, integer angle translation and the fixed real
coarse coordinates are composed on its target. -/
def IsNativeChart (e : OpenPartialHomeomorph (Coord r) (RealSpace (m := m) (a := a) (b := b) (S := S))) : Prop :=
  ∃ (q : Compactification (0 : Fin (n+1)) m) (o : Orbit 0 q) (ho : kind 0 q o = .paired)
    (z : Source hdim q o) (ha' : anchor q o ho = a) (hb' : reference q o ho = b)
    (hS' : PairedForestSimpleCluster.S q o ho = S) (k : ℤ),
    e = ((localChart hdim q o ho z).transHomeomorph
      ((productCast (m := m) ha' hb' hS').toHomeomorph.trans
        (turn (m := m) (a := a) (b := b) (S := S) k))).transHomeomorph InteriorGraphFaceCoordinates.toProduct.symm.toHomeomorph

include ha hb hba hanchor haMark hbMark in
/-- Unconditional exact target coverage of the full real simple face. -/
theorem exists_chart_at (y : Face (m := m) (a := a) (b := b) (S := S)) :
    ∃ e : OpenPartialHomeomorph (Coord r) (RealSpace (m := m) (a := a) (b := b) (S := S)),
      y.val ∈ e.target ∧ IsNativeChart hdim e := by
  have hy := openConditions_toAngular ha hba (toProduct y.val) y.property.1.2 y.property.2
  obtain ⟨o, ho, z, ha', hb', hS', k, hzs, he, hyt⟩ :=
    exists_product_chart hdim ha hb hba hanchor (toProduct y.val) hy haMark hbMark
  let e0 := (localChart hdim _ o ho z).transHomeomorph
    ((productCast (m := m) ha' hb' hS').toHomeomorph.trans
      (turn (m := m) (a := a) (b := b) (S := S) k))
  let e := e0.transHomeomorph InteriorGraphFaceCoordinates.toProduct.symm.toHomeomorph
  have he' : e z.val = y.val := by
    change InteriorGraphFaceCoordinates.toProduct.symm (e0 z.val) = y.val
    rw [he, ContinuousLinearEquiv.symm_apply_apply]
  exact ⟨e, he' ▸ e.map_source hzs, _, o, ho, z, ha', hb', hS', k, rfl⟩

def chartAt (y : Face (m := m) (a := a) (b := b) (S := S)) :=
  (exists_chart_at hdim ha hb hba hanchor haMark hbMark y).choose

theorem self_mem_target (y : Face (m := m) (a := a) (b := b) (S := S)) :
    y.val ∈ (chartAt hdim ha hb hba hanchor haMark hbMark y).target :=
  (exists_chart_at hdim ha hb hba hanchor haMark hbMark y).choose_spec.1

theorem chartAt_isNative (y : Face (m := m) (a := a) (b := b) (S := S)) :
    IsNativeChart hdim (chartAt hdim ha hb hba hanchor haMark hbMark y) :=
  (exists_chart_at hdim ha hb hba hanchor haMark hbMark y).choose_spec.2

theorem exists_countable_cover :
    ∃ c : Set (Face (m := m) (a := a) (b := b) (S := S)), c.Countable ∧
      Face (m := m) (a := a) (b := b) (S := S) ⊆
        ⋃ y ∈ c, (chartAt hdim ha hb hba hanchor haMark hbMark y).target := by
  apply (HereditarilyLindelofSpace.isLindelof (Face (m := m) (a := a) (b := b) (S := S))).elim_countable_subcover
    (fun y ↦ (chartAt hdim ha hb hba hanchor haMark hbMark y).target)
    (fun y ↦ (chartAt hdim ha hb hba hanchor haMark hbMark y).open_target)
  intro p hp
  exact mem_iUnion.mpr ⟨⟨p,hp⟩, self_mem_target hdim ha hb hba hanchor haMark hbMark ⟨p,hp⟩⟩

def centers := (exists_countable_cover hdim ha hb hba hanchor haMark hbMark).choose
instance : Countable (centers hdim ha hb hba hanchor haMark hbMark) :=
  (exists_countable_cover hdim ha hb hba hanchor haMark hbMark).choose_spec.1.to_subtype
instance : Encodable (centers hdim ha hb hba hanchor haMark hbMark) := Encodable.ofCountable _
abbrev Index := centers hdim ha hb hba hanchor haMark hbMark

def region (j : Index hdim ha hb hba hanchor haMark hbMark) : Set (RealSpace (m := m) (a := a) (b := b) (S := S)) :=
  Face (m := m) (a := a) (b := b) (S := S) ∩ (chartAt hdim ha hb hba hanchor haMark hbMark j.val).target

theorem measurableSet_region (j : Index hdim ha hb hba hanchor haMark hbMark) :
    MeasurableSet (region hdim ha hb hba hanchor haMark hbMark j) :=
  measurableSet_faceRegion.inter (chartAt hdim ha hb hba hanchor haMark hbMark j.val).open_target.measurableSet

theorem cover : Face (m := m) (a := a) (b := b) (S := S) =
    ⋃ j : Index hdim ha hb hba hanchor haMark hbMark, region hdim ha hb hba hanchor haMark hbMark j := by
  apply subset_antisymm
  · intro y hy
    obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.mp ((exists_countable_cover hdim ha hb hba hanchor haMark hbMark).choose_spec.2 hy)
    exact mem_iUnion.mpr ⟨⟨z,hz⟩, hy, hyz⟩
  · exact iUnion_subset fun j ↦ inter_subset_left

def piece (j : Index hdim ha hb hba hanchor haMark hbMark) : Set (RealSpace (m := m) (a := a) (b := b) (S := S)) :=
  region hdim ha hb hba hanchor haMark hbMark j \
    ⋃ k : Index hdim ha hb hba hanchor haMark hbMark,
      ⋃ (_ : Encodable.encode k < Encodable.encode j), region hdim ha hb hba hanchor haMark hbMark k

theorem measurableSet_piece (j : Index hdim ha hb hba hanchor haMark hbMark) :
    MeasurableSet (piece hdim ha hb hba hanchor haMark hbMark j) :=
  (measurableSet_region hdim ha hb hba hanchor haMark hbMark j).diff
    (MeasurableSet.iUnion fun k ↦ MeasurableSet.iUnion fun _ ↦ measurableSet_region hdim ha hb hba hanchor haMark hbMark k)

theorem pairwiseDisjoint_piece : Pairwise (fun j k ↦ Disjoint
    (piece hdim ha hb hba hanchor haMark hbMark j) (piece hdim ha hb hba hanchor haMark hbMark k)) := by
  intro j k hjk
  apply disjoint_left.mpr
  intro y hyj hyk
  have hcode : Encodable.encode j ≠ Encodable.encode k := fun h ↦ hjk (Encodable.encode_injective h)
  rcases lt_or_gt_of_ne hcode with hlt | hgt
  · exact hyk.2 (mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hlt, hyj.1⟩⟩)
  · exact hyj.2 (mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hgt, hyk.1⟩⟩)

theorem iUnion_piece :
    (⋃ j : Index hdim ha hb hba hanchor haMark hbMark, piece hdim ha hb hba hanchor haMark hbMark j) =
      Face (m := m) (a := a) (b := b) (S := S) := by
  apply subset_antisymm
  · exact iUnion_subset fun _ ↦ sdiff_subset.trans inter_subset_left
  · intro y hy
    have hex : ∃ t : ℕ, ∃ j : Index hdim ha hb hba hanchor haMark hbMark,
        Encodable.encode j = t ∧ y ∈ region hdim ha hb hba hanchor haMark hbMark j := by
      rw [cover hdim ha hb hba hanchor haMark hbMark] at hy
      obtain ⟨j,hj⟩ := mem_iUnion.mp hy
      exact ⟨_,j,rfl,hj⟩
    obtain ⟨j,hj,hyj⟩ := Nat.find_spec hex
    refine mem_iUnion.mpr ⟨j,hyj,?_⟩
    intro h
    obtain ⟨k,hkj,hyk⟩ := mem_iUnion₂.mp h
    exact Nat.find_min hex (hj ▸ hkj) ⟨k,rfl,hyk⟩

/-- Countable integration over the full simple face uses a proved disjoint
native-chart cover; coverage and summability are not supplied as hypotheses. -/
theorem hasSum_integral_piece (f : RealSpace (m := m) (a := a) (b := b) (S := S) → ℝ)
    (hf : IntegrableOn f (Face (m := m) (a := a) (b := b) (S := S))) :
    HasSum (fun j : Index hdim ha hb hba hanchor haMark hbMark ↦
      ∫ y in piece hdim ha hb hba hanchor haMark hbMark j, f y)
      (∫ y in Face (m := m) (a := a) (b := b) (S := S), f y) := by
  have hcov := iUnion_piece hdim ha hb hba hanchor haMark hbMark
  simpa only [hcov] using hasSum_integral_iUnion
    (measurableSet_piece hdim ha hb hba hanchor haMark hbMark)
    (pairwiseDisjoint_piece hdim ha hb hba hanchor haMark hbMark)
    (show IntegrableOn f (⋃ j : Index hdim ha hb hba hanchor haMark hbMark,
      piece hdim ha hb hba hanchor haMark hbMark j) from hcov.symm ▸ hf)

include ha hb hanchor in
/-- Every selected translated real chart preserves the literal full DR map
on its entire native source. Thus the new target cover is a geometric cover,
not just a family of unrelated open sets. -/
theorem nativeChart_ambient
    (e : OpenPartialHomeomorph (Coord r) (RealSpace (m := m) (a := a) (b := b) (S := S)))
    (he : IsNativeChart hdim e) :
    ∃ (q : Compactification (0 : Fin (n+1)) m) (o : Orbit 0 q) (ho : kind 0 q o = .paired)
      (z : Source hdim q o),
      e.source = (localChart hdim q o ho z).source ∧
      ∀ w ∈ e.source, InteriorFaceDRCoordinates.ambient (InteriorGraphFaceCoordinates.toProduct (e w)) =
        ForestRadialFaceImmersion.forward hdim q o w := by
  obtain ⟨q,o,ho,z,ha',hb',hS',k,rfl⟩ := he
  refine ⟨q,o,ho,z,rfl,?_⟩
  intro w hw
  let p := localChart hdim q o ho z w
  let C := productCast (i := (0 : Fin (n+1))) (m := m) ha' hb' hS'
  have hp : (toAngular p).toFree.OpenConditions :=
    PairedForestProductOverlap.toProduct_openConditions hdim q o ho (phase hdim q o ho z)
      ⟨w,localChart_source_subset hdim q o ho z hw⟩
  have hpC := openConditions_productCast ha' hb' hS' p hp
  change InteriorFaceDRCoordinates.ambient
    (InteriorGraphFaceCoordinates.toProduct (InteriorGraphFaceCoordinates.toProduct.symm
      (turn (m := m) (a := a) (b := b) (S := S) k (C p)))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply, ambient_turn ha hb hanchor k (C p) hpC,
    ambient_productCast]
  exact PairedForestProductOverlap.ambient_toProduct hdim q o ho (phase hdim q o ho z)
    ⟨w,localChart_source_subset hdim q o ho z hw⟩

include ha hb hanchor in
/-- In particular every original ambient cutoff is preserved by the entire
translated chart, including cutoffs belonging to a different forest center. -/
theorem nativeChart_cutoff
    (e : OpenPartialHomeomorph (Coord r) (RealSpace (m := m) (a := a) (b := b) (S := S)))
    (he : IsNativeChart hdim e) (ρ : OriginalPartitionCancellation.Ambient n m → ℝ) :
    ∃ (q : Compactification (0 : Fin (n+1)) m) (o : Orbit 0 q) (ho : kind 0 q o = .paired)
      (z : Source hdim q o),
      e.source = (localChart hdim q o ho z).source ∧
      ∀ w ∈ e.source,
        ρ (CompactDRCoordinates.realCoordinates (n+1) m
          (InteriorFaceDRCoordinates.ambient (InteriorGraphFaceCoordinates.toProduct (e w)))) =
        ρ (CompactDRCoordinates.realCoordinates (n+1) m (ForestRadialFaceImmersion.forward hdim q o w)) := by
  obtain ⟨q,o,ho,z,hs,hDR⟩ := nativeChart_ambient hdim ha hb hanchor e he
  exact ⟨q,o,ho,z,hs, fun w hw ↦ congrArg (fun v ↦ ρ (CompactDRCoordinates.realCoordinates (n+1) m v)) (hDR w hw)⟩

/-- The cover applies to every original partition-weighted two-point density,
with L1 derived from the actual circle/coarse integral endpoint. -/
theorem hasSum_localizedDensity_twoPoint {J : Type*} [Fintype J]
    (ρ : Partition J (0 : Fin (n+1)) m) (j : J)
    (edges : Fin (shapeDegree a b S + coarseDegree (0 : Fin (n+1)) a S m) → Edge (n+1) m)
    (hcount : Fintype.card {q // IsInternal S (edges q)} = shapeDegree a b S)
    (hS : S.card = 2) (hne : ∀ q, (edges q).2 ≠ Sum.inl (edges q).1) :
    HasSum (fun k : Index hdim ha hb hba hanchor haMark hbMark ↦
      ∫ y in piece hdim ha hb hba hanchor haMark hbMark k,
        localizedDensity ρ ha hb hba hanchor edges j y)
      (∫ y in Face (m := m) (a := a) (b := b) (S := S), localizedDensity ρ ha hb hba hanchor edges j y) :=
  hasSum_integral_piece hdim ha hb hba hanchor haMark hbMark _
    ((TwoPointFacePartitionReassembly.sum_integral_localizedDensity_twoPoint
      ρ ha hb hba hanchor edges hcount hS hne).1 j)

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestSimpleProductCover
