import EnvelopingIsomorphism.Deformation.MainFixedSimpleChartTransfer
import EnvelopingIsomorphism.Deformation.MainPairedChartTransfer

/-! A physical real collision mask determines a unique radial orbit in every
original Stokes chart. Nonzero cutoffs provide the actual source parameters
for proper-real, pure-boundary and infinity families. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MainRealSupportOrbit
open Kontsevich Configuration ExtractedForestParameters ExtractedForestFrames
open ForestRadialFaceClassification MainScalarBoundaryAssembly MainFixedSimpleChartTransfer
open ReflectedRadiusCoordinates
open scoped Classical

theorem orbit_eq_of_representative_mask {n m : ℕ}
    (x : Compactification (0 : Fin (n+1)) m) (o p : Orbit 0 x)
    (h : (representative 0 x o).val.val = (representative 0 x p).val.val) : o = p := by
  have he : representative 0 x o = representative 0 x p :=
    Subtype.ext (Subtype.ext h)
  exact (representative_orbit 0 x o).symm.trans
    ((congrArg (orbitClass (tree 0 x) (reflection 0 x) (reflection_reflection 0 x)) he).trans
      (representative_orbit 0 x p))

variable {n : ℕ} {H : UniformBinaryGraphs.BinaryGraph (n+2) 3}
    (P : MainPartition H) (j : P.charts) {A : Type*}

private theorem supported_orbit (q : A → Compactification (0 : Fin (n+2)) 3)
    (mask : Finset (DoubledLabel (n+2) 3)) (k : Kind)
    (hsource : ∀ a, CompactDRAmbientPartition.cutoff 0 (P.partition j) (q a) ≠ 0 →
      ∃ (o : Orbit 0 j.val) (z : ForestRadialFaceLocalization.source (main_dimension n) j.val o),
        kind 0 j.val o = k ∧ (representative 0 j.val o).val.val = mask ∧
        PairedForestSimpleOverlap.facePoint (main_dimension n) j.val o z = q a)
    (hne : ∃ a, CompactDRAmbientPartition.cutoff 0 (P.partition j) (q a) ≠ 0) :
    ∃ o : Orbit 0 j.val, kind 0 j.val o = k ∧
      (representative 0 j.val o).val.val = mask ∧
      ∀ a, CompactDRAmbientPartition.cutoff 0 (P.partition j) (q a) ≠ 0 →
        ∃ z : ForestRadialFaceLocalization.source (main_dimension n) j.val o,
          PairedForestSimpleOverlap.facePoint (main_dimension n) j.val o z = q a := by
  obtain ⟨a₀,ha₀⟩ := hne
  obtain ⟨o,z,ho,hm,hz⟩ := hsource a₀ ha₀
  refine ⟨o,ho,hm,?_⟩
  intro a ha
  obtain ⟨p,w,hp,hm',hw⟩ := hsource a ha
  have he : p = o := orbit_eq_of_representative_mask j.val p o (hm'.trans hm.symm)
  subst p
  exact ⟨w,hw⟩

/-- The exterior anchor may differ from the ambient chart's anchor zero. -/
theorem properReal_exists_fixed_supported_orbit {i a : Fin (n+2)}
    {S : Finset (Fin (n+2))} {l u : Fin 4}
    (D : A → BoundaryClusterData i a 3 S l u)
    (hne : ∃ t, CompactDRAmbientPartition.cutoff 0 (P.partition j)
      (anchorHomeomorph i 0 (D t).boundaryPoint) ≠ 0) :
    ∃ o : Orbit 0 j.val, kind 0 j.val o = .properReal ∧
      (representative 0 j.val o).val.val = collisionMask S l u ∧
      ∀ t, CompactDRAmbientPartition.cutoff 0 (P.partition j)
        (anchorHomeomorph i 0 (D t).boundaryPoint) ≠ 0 →
        ∃ z : ForestRadialFaceLocalization.source (main_dimension n) j.val o,
          PairedForestSimpleOverlap.facePoint (main_dimension n) j.val o z =
            anchorHomeomorph i 0 (D t).boundaryPoint := by
  apply supported_orbit P j _ _ _ ?_ hne
  intro t ht
  exact properReal_source_changeAnchor (main_dimension n) j.val (D t)
    (MainPairedChartTransfer.mem_chart_of_cutoff_ne_zero P j _ ht)

theorem pureBoundary_exists_fixed_supported_orbit {a b : Fin 3} {l u : Fin 4}
    (D : A → PureBoundaryClusterData (0 : Fin (n+2)) 3 l u a b)
    (hne : ∃ t, CompactDRAmbientPartition.cutoff 0 (P.partition j) (D t).boundaryPoint ≠ 0) :
    ∃ o : Orbit 0 j.val, kind 0 j.val o = .pureBoundary ∧
      (representative 0 j.val o).val.val = collisionMask ∅ l u ∧
      ∀ t, CompactDRAmbientPartition.cutoff 0 (P.partition j) (D t).boundaryPoint ≠ 0 →
        ∃ z : ForestRadialFaceLocalization.source (main_dimension n) j.val o,
          PairedForestSimpleOverlap.facePoint (main_dimension n) j.val o z = (D t).boundaryPoint := by
  apply supported_orbit P j _ _ _ ?_ hne
  intro t ht
  exact pureBoundary_source (main_dimension n) j.val (D t)
    (MainPairedChartTransfer.mem_chart_of_cutoff_ne_zero P j _ ht)

theorem infinity_exists_fixed_supported_orbit {a : Fin 3} {l u : Fin 4}
    (D : A → BoundaryAnchoredInfinityData (0 : Fin (n+2)) 3 l u a)
    (hne : ∃ t, CompactDRAmbientPartition.cutoff 0 (P.partition j)
      ((D t).compactInsertion (D t).admissibleScale_zero) ≠ 0) :
    ∃ o : Orbit 0 j.val, kind 0 j.val o = .infinity ∧
      (representative 0 j.val o).val.val = collisionMask Finset.univ l u ∧
      ∀ t, CompactDRAmbientPartition.cutoff 0 (P.partition j)
        ((D t).compactInsertion (D t).admissibleScale_zero) ≠ 0 →
        ∃ z : ForestRadialFaceLocalization.source (main_dimension n) j.val o,
          PairedForestSimpleOverlap.facePoint (main_dimension n) j.val o z =
            (D t).compactInsertion (D t).admissibleScale_zero := by
  apply supported_orbit P j _ _ _ ?_ hne
  intro t ht
  exact infinity_source (main_dimension n) j.val (D t)
    (MainPairedChartTransfer.mem_chart_of_cutoff_ne_zero P j _ ht)

end EnvelopingIsomorphism.Deformation.MainRealSupportOrbit
