import EnvelopingIsomorphism.Deformation.MainSimplePairedChartTransfer

/-! A fixed physical cluster mask determines at most one paired radial orbit
in each original chart. Thus every nonzero cutoff point of that cluster uses
the same orbit, even though the source parameters and physical points vary. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.MainPairedSupportOrbit

open Kontsevich Configuration ExtractedForestParameters ExtractedForestFrames
open ForestRadialFaceClassification ForestRadialClusterLabels
open ReflectedRadiusCoordinates MainScalarBoundaryAssembly
open scoped Classical

theorem paired_orbit_eq_of_mask {n m : ℕ}
    (x : Compactification (0 : Fin (n + 1)) m)
    (o p : Orbit 0 x) (ho : kind 0 x o = .paired) (hp : kind 0 x p = .paired)
    (h : PairedForestSimpleCluster.S x o ho = PairedForestSimpleCluster.S x p hp) : o = p := by
  have hu : (upperNode 0 x o ho).val = (upperNode 0 x p hp).val := by
    apply Subtype.ext
    rw [isUpper_label_eq_image 0 x _ (upperNode_spec 0 x o ho).2,
      isUpper_label_eq_image 0 x _ (upperNode_spec 0 x p hp).2]
    change (PairedForestSimpleCluster.S x o ho).image _ =
      (PairedForestSimpleCluster.S x p hp).image _
    rw [h]
  have hu' : upperNode 0 x o ho = upperNode 0 x p hp := Subtype.ext hu
  exact (upperNode_spec 0 x o ho).1.symm.trans
    ((congrArg (orbitClass (tree 0 x) (reflection 0 x) (ExtractedForestFrames.reflection_reflection 0 x))
      hu').trans (upperNode_spec 0 x p hp).1)

variable {n : ℕ} {H : UniformBinaryGraphs.BinaryGraph (n + 2) 3}
    (P : MainPartition H) (j : P.charts)
    {S : Finset (Fin (n + 2))} {A : Type*}
    (D : A → SingleInteriorCluster (0 : Fin (n + 2)) 3 S)

/-- No orbit matching or source transfer premise is supplied. The actual
nonzero-cutoff transfer theorem constructs all source parameters, and the
physical mask proves that their orbit is constant on the weighted family. -/
theorem exists_fixed_supported_orbit (hS : 1 < S.card)
    (hne : ∃ a : A, CompactDRAmbientPartition.cutoff 0 (P.partition j)
      (D a).toInteriorCollisionData.boundaryPoint ≠ 0) :
    ∃ (o : Orbit 0 j.val) (ho : kind 0 j.val o = .paired),
      PairedForestSimpleCluster.S j.val o ho = S ∧
      ∀ a : A, CompactDRAmbientPartition.cutoff 0 (P.partition j)
        (D a).toInteriorCollisionData.boundaryPoint ≠ 0 →
        ∃ z : ForestRadialFaceLocalization.source (main_dimension n) j.val o,
          PairedForestSimpleOverlap.facePoint (main_dimension n) j.val o z =
            (D a).toInteriorCollisionData.boundaryPoint := by
  obtain ⟨a₀, ha₀⟩ := hne
  obtain ⟨o, ho, z₀, hmask, hz₀⟩ :=
    MainSimplePairedChartTransfer.hasPairedSource_of_cutoff P j (D a₀) hS ha₀
  refine ⟨o, ho, hmask, ?_⟩
  intro a ha
  obtain ⟨p, hp, z, hmask', hz⟩ :=
    MainSimplePairedChartTransfer.hasPairedSource_of_cutoff P j (D a) hS ha
  have he : p = o := paired_orbit_eq_of_mask j.val p o hp ho (hmask'.trans hmask.symm)
  subst p
  exact ⟨z, hz⟩

/-- The absence of supported points is pointwise zero weight, rather than
an assumption that an arbitrary weighted integral vanishes. -/
theorem cutoff_zero_of_no_supported_point
    (hne : ¬ ∃ a : A, CompactDRAmbientPartition.cutoff 0 (P.partition j)
      (D a).toInteriorCollisionData.boundaryPoint ≠ 0) (a : A) :
    CompactDRAmbientPartition.cutoff 0 (P.partition j)
      (D a).toInteriorCollisionData.boundaryPoint = 0 := by
  by_contra ha
  exact hne ⟨a, ha⟩

end EnvelopingIsomorphism.Deformation.MainPairedSupportOrbit
