import EnvelopingIsomorphism.Deformation.Kontsevich.SimpleProductPhaseIdentification

/-! A global open atlas of a canonically marked simple face by actual native
paired forest charts, allowing integer angle translates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.SimpleFaceNativeAtlas
open Configuration InteriorGraphFaceCoordinates PairedForestSimpleCluster
open PairedForestSmoothProduct PairedForestProductChart PairedForestCanonicalMarks
open SimpleProductPhaseIdentification Set MeasureTheory
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)

set_option genInjectivity false in
structure ChartIndex (a b : Fin (n + 1)) (T : Finset (Fin (n + 1))) : Type where
  center : Compactification (0 : Fin (n + 1)) m
  orbit : ForestRadialFaceClassification.Orbit 0 center
  paired : ForestRadialFaceClassification.kind 0 center orbit = .paired
  point : {z : BoxStokes.Coord r // z ∈ ForestRadialFaceLocalization.source hdim center orbit}
  labels : S center orbit paired = T
  anchor_eq : anchor center orbit paired = a
  reference_eq : reference center orbit paired = b
  turn : ℤ

variable {a b : Fin (n + 1)} {T : Finset (Fin (n + 1))}

def nativeEquiv (c : ChartIndex hdim a b T) :
    Product c.center c.orbit c.paired ≃L[ℝ] ProductCoordinates 0 a b T m := by
  rcases c with ⟨x, o, ho, z, hT, ha, hb, k⟩
  dsimp only
  subst T; subst a; subst b
  exact ContinuousLinearEquiv.refl ℝ _

theorem nativeEquiv_shift (c : ChartIndex hdim a b T)
    (k : ℤ) (p : Product c.center c.orbit c.paired) :
    nativeEquiv hdim c (shift k p) = shift k (nativeEquiv hdim c p) := by
  rcases c with ⟨x, o, ho, z, hT, ha, hb, k'⟩
  subst T; subst a; subst b
  rfl

def shiftHomeomorph (k : ℤ) : ProductCoordinates 0 a b T m ≃ₜ ProductCoordinates 0 a b T m where
  toFun := shift k
  invFun := shift (-k)
  left_inv p := by ext <;> simp [shift]
  right_inv p := by ext <;> simp [shift]
  continuous_toFun := by unfold shift; fun_prop
  continuous_invFun := by unfold shift; fun_prop

def targetHomeomorph (c : ChartIndex hdim a b T) :
    Product c.center c.orbit c.paired ≃ₜ ProductCoordinates 0 a b T m :=
  (nativeEquiv hdim c).toHomeomorph.trans (shiftHomeomorph c.turn)

def region (c : ChartIndex hdim a b T) : Set (ProductCoordinates 0 a b T m) :=
  targetHomeomorph hdim c '' (localChart hdim c.center c.orbit c.paired c.point).target

theorem isOpen_region (c : ChartIndex hdim a b T) : IsOpen (region hdim c) :=
  (targetHomeomorph hdim c).isOpenMap _ (localChart hdim c.center c.orbit c.paired c.point).open_target

/-- Transport across literally equal marked label sets preserves the genuine
simple-face point, rather than introducing a coordinate agreement assumption. -/
theorem nativeEquiv_openConditions (c : ChartIndex hdim a b T)
    (p : Product c.center c.orbit c.paired) :
    (toAngular (nativeEquiv hdim c p)).toFree.OpenConditions ↔ (toAngular p).toFree.OpenConditions := by
  rcases c with ⟨x, o, ho, z, hT, ha, hb, k⟩
  subst T; subst a; subst b
  rfl

theorem nativeEquiv_boundaryPoint (c : ChartIndex hdim a b T)
    (ha : a ∈ T) (hb : b ∈ T) (hanchor : (0 : Fin (n + 1)) ∈ T → a = 0)
    (p : Product c.center c.orbit c.paired) (hp : (toAngular p).toFree.OpenConditions) :
    (InteriorFaceDRCoordinates.datum ha hb hanchor (nativeEquiv hdim c p)
      ((nativeEquiv_openConditions hdim c p).mpr hp)).toInteriorCollisionData.boundaryPoint =
    (InteriorFaceDRCoordinates.datum (anchor_mem c.center c.orbit c.paired)
      (reference_mem c.center c.orbit c.paired) (anchor_global c.center c.orbit c.paired) p hp).toInteriorCollisionData.boundaryPoint := by
  rcases c with ⟨x, o, ho, z, hT, hA, hB, k⟩
  subst T; subst a; subst b
  rfl

/-- Every simple product point is covered by a translated native paired chart.
The native center and orbit come from the proved extracted-forest coverage. -/
theorem exists_region (hT : 1 < T.card)
    (p : ProductCoordinates 0 (canonicalAnchor T) (canonicalReference T) T m)
    (hp : (toAngular p).toFree.OpenConditions) :
    ∃ c : ChartIndex hdim (canonicalAnchor T) (canonicalReference T) T, p ∈ region hdim c := by
  have ha := canonicalAnchor_mem T (Finset.card_pos.mp (by omega : 0 < T.card))
  have hb := canonicalReference_mem T hT
  have hba := canonicalReference_ne T hT
  have hg : (0 : Fin (n + 1)) ∈ T → canonicalAnchor T = 0 := by
    intro h; simp [canonicalAnchor, h]
  let D := InteriorFaceDRCoordinates.datum ha hb hg p hp
  obtain ⟨o, ho, z, hS, hz⟩ :=
    SingleInteriorExtractedPartitions.canonicalDatum_exists_source_with_mask hdim ha hb hba hg p hp
  let c₀ : ChartIndex hdim (canonicalAnchor T) (canonicalReference T) T :=
    ⟨D.toInteriorCollisionData.boundaryPoint, o, ho, z, hS,
      (anchor_eq_canonical _ _ _).trans (congrArg canonicalAnchor hS),
      (reference_eq_canonical _ _ _).trans (congrArg canonicalReference hS), 0⟩
  let q := (nativeEquiv hdim c₀).symm p
  have hq : (toAngular q).toFree.OpenConditions := by
    apply (nativeEquiv_openConditions hdim c₀ q).mp
    simpa only [q, ContinuousLinearEquiv.apply_symm_apply] using hp
  have he := nativeEquiv_boundaryPoint hdim c₀ ha hb hg q hq
  simp only [q, ContinuousLinearEquiv.apply_symm_apply] at he
  have hn : (InteriorFaceDRCoordinates.datum (anchor_mem c₀.center c₀.orbit c₀.paired)
      (reference_mem c₀.center c₀.orbit c₀.paired) (anchor_global c₀.center c₀.orbit c₀.paired) q hq).toInteriorCollisionData.boundaryPoint =
        PairedForestSimpleOverlap.facePoint hdim c₀.center c₀.orbit c₀.point := he.symm.trans hz.symm
  obtain ⟨k, y, hy, heq⟩ := mem_shift_localChart_target hdim c₀.center c₀.orbit c₀.paired q hq c₀.point hn
  let c : ChartIndex hdim (canonicalAnchor T) (canonicalReference T) T := { c₀ with turn := k }
  refine ⟨c, y, hy, ?_⟩
  change shift k (nativeEquiv hdim c y) = p
  rw [← nativeEquiv_shift hdim c k y, heq]
  exact (nativeEquiv hdim c₀).apply_symm_apply p


/-- The native chart as a chart in the common real product coordinates. -/
def realChart (c : ChartIndex hdim a b T) :
    OpenPartialHomeomorph (BoxStokes.Coord r) (RealProductCoordinates 0 a b T m) :=
  ((localChart hdim c.center c.orbit c.paired c.point).trans
    (targetHomeomorph hdim c).toOpenPartialHomeomorph).trans
      (InteriorGraphFaceCoordinates.toProduct.symm.toHomeomorph.toOpenPartialHomeomorph)

theorem realChart_source (c : ChartIndex hdim a b T) :
    (realChart hdim c).source = (localChart hdim c.center c.orbit c.paired c.point).source := by
  simp only [realChart, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, preimage_univ, inter_univ]

theorem realChart_target (c : ChartIndex hdim a b T) :
    (realChart hdim c).target = InteriorGraphFaceCoordinates.toProduct ⁻¹' region hdim c := by
  ext p
  simp only [realChart, OpenPartialHomeomorph.trans_target, Homeomorph.toOpenPartialHomeomorph_target,
    mem_inter_iff, mem_univ, true_and, mem_preimage]
  change (targetHomeomorph hdim c).symm (InteriorGraphFaceCoordinates.toProduct p) ∈
    (localChart hdim c.center c.orbit c.paired c.point).target ↔ _
  constructor
  · intro h
    exact ⟨(targetHomeomorph hdim c).symm (InteriorGraphFaceCoordinates.toProduct p), h,
      (targetHomeomorph hdim c).apply_symm_apply _⟩
  · rintro ⟨q, hq, heq⟩
    rw [← heq, Homeomorph.symm_apply_apply]
    exact hq

abbrev CanonicalIndex (T : Finset (Fin (n + 1))) :=
  ChartIndex hdim (canonicalAnchor T) (canonicalReference T) T

open InteriorFacePartitionReassembly
variable (T) (hT : 1 < T.card)

include hT in
theorem exists_countable_cover : ∃ c : Set (CanonicalIndex hdim T), c.Countable ∧
    FaceRegion 0 (canonicalAnchor T) (canonicalReference T) T m ⊆
      ⋃ z ∈ c, (realChart hdim z).target := by
  apply (HereditarilyLindelofSpace.isLindelof
    (FaceRegion 0 (canonicalAnchor T) (canonicalReference T) T m)).elim_countable_subcover
      (fun z : CanonicalIndex hdim T ↦ (realChart hdim z).target)
      (fun z ↦ (realChart hdim z).open_target)
  intro p hp
  have ha := canonicalAnchor_mem T (Finset.card_pos.mp (by omega : 0 < T.card))
  have hba := canonicalReference_ne T hT
  have hop := openConditions_toAngular ha hba (InteriorGraphFaceCoordinates.toProduct p) hp.1.2 hp.2
  obtain ⟨c, hc⟩ := exists_region hdim hT (InteriorGraphFaceCoordinates.toProduct p) hop
  exact mem_iUnion.mpr ⟨c, by rwa [realChart_target]⟩

def centers : Set (CanonicalIndex hdim T) := (exists_countable_cover hdim T hT).choose
instance : Countable (centers hdim T hT) := (exists_countable_cover hdim T hT).choose_spec.1.to_subtype
instance : Encodable (centers hdim T hT) := Encodable.ofCountable _
abbrev Index := centers hdim T hT

def piece (j : Index hdim T hT) : Set (RealProductCoordinates 0 (canonicalAnchor T) (canonicalReference T) T m) :=
  (FaceRegion 0 (canonicalAnchor T) (canonicalReference T) T m ∩ (realChart hdim j.val).target) \
    ⋃ k : Index hdim T hT, ⋃ (_ : Encodable.encode k < Encodable.encode j), (realChart hdim k.val).target

theorem piece_subset_target (j : Index hdim T hT) : piece hdim T hT j ⊆ (realChart hdim j.val).target :=
  fun _ h ↦ h.1.2

theorem measurableSet_piece (j : Index hdim T hT) : MeasurableSet (piece hdim T hT j) :=
  (measurableSet_faceRegion.inter (realChart hdim j.val).open_target.measurableSet).diff
    (MeasurableSet.iUnion fun k ↦ MeasurableSet.iUnion fun _ ↦ (realChart hdim k.val).open_target.measurableSet)

theorem pairwiseDisjoint_piece : Pairwise (fun j k : Index hdim T hT ↦
    Disjoint (piece hdim T hT j) (piece hdim T hT k)) := by
  intro j k hjk
  apply disjoint_left.mpr
  intro p hpj hpk
  have hcode : Encodable.encode j ≠ Encodable.encode k := fun h ↦ hjk (Encodable.encode_injective h)
  rcases lt_or_gt_of_ne hcode with hlt | hgt
  · exact hpk.2 (mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hlt, hpj.1.2⟩⟩)
  · exact hpj.2 (mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hgt, hpk.1.2⟩⟩)

theorem iUnion_piece : (⋃ j : Index hdim T hT, piece hdim T hT j) =
    FaceRegion 0 (canonicalAnchor T) (canonicalReference T) T m := by
  apply subset_antisymm
  · exact iUnion_subset fun _ _ hp ↦ hp.1.1
  · intro p hp
    have hex : ∃ a : ℕ, ∃ j : Index hdim T hT,
        Encodable.encode j = a ∧ p ∈ (realChart hdim j.val).target := by
      obtain ⟨c, hc, hpc⟩ := mem_iUnion₂.mp ((exists_countable_cover hdim T hT).choose_spec.2 hp)
      exact ⟨Encodable.encode (⟨c, hc⟩ : Index hdim T hT), ⟨c, hc⟩, rfl, hpc⟩
    obtain ⟨j, hj, hpj⟩ := Nat.find_spec hex
    refine mem_iUnion.mpr ⟨j, ⟨hp, hpj⟩, ?_⟩
    intro h
    obtain ⟨k, hkj, hpk⟩ := mem_iUnion₂.mp h
    exact Nat.find_min hex (hj ▸ hkj) ⟨k, rfl, hpk⟩

/-- A piece in the original native radial face coordinates. -/
def nativePiece (j : Index hdim T hT) : Set (BoxStokes.Coord r) :=
  (realChart hdim j.val).source ∩ (realChart hdim j.val) ⁻¹' piece hdim T hT j

theorem nativePiece_subset_source (j : Index hdim T hT) :
    nativePiece hdim T hT j ⊆ Source hdim j.val.center j.val.orbit := by
  intro w hw
  apply localChart_source_subset hdim j.val.center j.val.orbit j.val.paired j.val.point
  simpa only [realChart_source] using hw.1

theorem image_nativePiece (j : Index hdim T hT) :
    realChart hdim j.val '' nativePiece hdim T hT j = piece hdim T hT j := by
  apply subset_antisymm
  · rintro _ ⟨w, hw, rfl⟩; exact hw.2
  · intro p hp
    have ht := piece_subset_target hdim T hT j hp
    refine ⟨(realChart hdim j.val).symm p, ⟨(realChart hdim j.val).map_target ht, ?_⟩,
      (realChart hdim j.val).right_inv ht⟩
    change realChart hdim j.val ((realChart hdim j.val).symm p) ∈ piece hdim T hT j
    rwa [(realChart hdim j.val).right_inv ht]

/-- Exact countable integral decomposition into actual native-chart images. -/
theorem hasSum_integral_native_images
    (f : RealProductCoordinates 0 (canonicalAnchor T) (canonicalReference T) T m → ℝ)
    (hf : IntegrableOn f (FaceRegion 0 (canonicalAnchor T) (canonicalReference T) T m)) :
    HasSum (fun j : Index hdim T hT ↦
      ∫ p in realChart hdim j.val '' nativePiece hdim T hT j, f p)
      (∫ p in FaceRegion 0 (canonicalAnchor T) (canonicalReference T) T m, f p) := by
  simp only [image_nativePiece]
  have h := hasSum_integral_iUnion (measurableSet_piece hdim T hT)
    (pairwiseDisjoint_piece hdim T hT)
    (show IntegrableOn f (⋃ j : Index hdim T hT, piece hdim T hT j) from
      (iUnion_piece hdim T hT).symm ▸ hf)
  simpa only [iUnion_piece] using h

/-- Every fixed member of the actual finite ambient partition decomposes on
the global native atlas. The full localized integral, not its individual
weighted pieces, is the value of the sum. -/
theorem hasSum_localizedDensity_native_images
    {J : Type*} [Fintype J] (P : Partition J (0 : Fin (n + 1)) m)
    (edges : Fin (shapeDegree (canonicalAnchor T) (canonicalReference T) T +
      coarseDegree 0 (canonicalAnchor T) T m) → Edge (n + 1) m)
    (hcount : Fintype.card {q // IsInternal T (edges q)} = shapeDegree (canonicalAnchor T) (canonicalReference T) T)
    (hlarge : 3 ≤ T.card) (hne : ∀ q, (edges q).2 ≠ Sum.inl (edges q).1) (j : J) :
    let ha := canonicalAnchor_mem T (Finset.card_pos.mp (by omega : 0 < T.card))
    let hb := canonicalReference_mem T hT
    let hba := canonicalReference_ne T hT
    let hg : (0 : Fin (n + 1)) ∈ T → canonicalAnchor T = 0 := fun h ↦ by simp [canonicalAnchor, h]
    HasSum (fun c : Index hdim T hT ↦
      ∫ p in realChart hdim c.val '' nativePiece hdim T hT c,
        localizedDensity P ha hb hba hg edges j p)
      (∫ p in FaceRegion 0 (canonicalAnchor T) (canonicalReference T) T m,
        localizedDensity P ha hb hba hg edges j p) := by
  dsimp only
  apply hasSum_integral_native_images
  exact integrableOn_localizedDensity P _ _ _ _ edges hcount hlarge hne j

end EnvelopingIsomorphism.Deformation.Kontsevich.SimpleFaceNativeAtlas
