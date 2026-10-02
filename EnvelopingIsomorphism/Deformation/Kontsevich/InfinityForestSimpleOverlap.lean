import EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestSimpleCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.InfinityBoundaryFaceDR
import EnvelopingIsomorphism.Deformation.Kontsevich.InfinityBoundaryGraphFactorization
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-! Actual smooth local coordinate equivalence for a strict all-interior
infinity forest face, with the full-DR decoder as explicit inverse. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestSimpleOverlap
open Configuration ForestRadialFaceClassification InfinityForestSimpleCoordinates
open InfinityForestSimpleCluster (lower upper)
open BoxStokes
open scoped Classical Topology
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : ForestRadialFaceClassification.Orbit 0 x) (q : Fin m)

abbrev Face (_x : Compactification (0 : Fin (n+1)) m) (_o : ForestRadialFaceClassification.Orbit 0 _x) (q : Fin m) :=
  BoundaryAnchoredInfinityFreeCoordinates.FaceCoordinates (0 : Fin (n+1)) m q

def inverse (y : Face x o q) : Coord r :=
  ForestRadialFaceImmersion.inverse hdim x o (InfinityBoundaryFaceDR.ambient (lower x o) (upper x o) y)

variable (ho : kind 0 x o = .infinity)
  (hq : q ∉ boundaryClusterBlock (lower x o) (upper x o))
  (hne : (boundaryClusterBlock (lower x o) (upper x o)).Nonempty)
  (z : ForestRadialFaceLocalization.source hdim x o)

include ho hq hne in
theorem ambient_coordinates :
    InfinityBoundaryFaceDR.ambient (lower x o) (upper x o) (coordinates hdim x o q z.val) =
      ForestRadialFaceImmersion.forward hdim x o z.val := by
  rw [InfinityBoundaryFaceDR.ambient_eq_data _ _ _ (coordinates_mem_source hdim x o q ho hq hne z)]
  have hfree : BoundaryAnchoredInfinityFreeCoordinates.faceDomain (coordinates hdim x o q z.val)
      (coordinates_mem_source hdim x o q ho hq hne z) =
      InfinityForestSimpleCluster.freeDomain hdim x o ho q hq hne z :=
    Subtype.ext (coordinates_eq_freeDomain hdim x o q ho hq hne z)
  rw [hfree]
  simp only [InfinityForestSimpleCluster.freeDomain, BoundaryAnchoredInfinityFreeDomain.toDomain_toFreeDomain]
  rw [InfinityForestResolvedCoordinates.insertion_DR_eq_native, ForestRadialFaceImmersion.forward_data]

include ho hq hne in
theorem contDiffAt_inverse : ContDiffAt ℝ ⊤ (inverse hdim x o q) (coordinates hdim x o q z.val) := by
  have h := ForestRadialFaceImmersion.contDiffAt_inverse hdim x o z
  rw [← ambient_coordinates hdim x o q ho hq hne z] at h
  exact h.comp _ (InfinityBoundaryFaceDR.contDiffAt_ambient _ _ _ (coordinates_mem_source hdim x o q ho hq hne z))

include hdim ho hq hne in
theorem finrank_face : Module.finrank ℝ (Face x o q) = r := by
  rw [InfinityBoundaryGraphFactorization.finrank_face]
  change 2 * ((n+1)-1) + (m-1) = r
  have hm := q.isLt
  change n * 2 + m = r + 1 at hdim
  omega

include ho hq hne in
theorem inverse_coordinates : inverse hdim x o q (coordinates hdim x o q z.val) = z.val := by
  rw [inverse, ambient_coordinates hdim x o q ho hq hne z]
  exact ForestRadialFaceImmersion.inverse_forward hdim x o z

include ho hq hne in
theorem differential_leftInverse :
    (fderiv ℝ (inverse hdim x o q) (coordinates hdim x o q z.val)).comp
      (fderiv ℝ (coordinates hdim x o q) z.val) = ContinuousLinearMap.id ℝ (Coord r) := by
  have hd := ((contDiffAt_inverse hdim x o q ho hq hne z).differentiableAt (by simp)).hasFDerivAt.comp z.val
    ((contDiffAt_coordinates hdim x o q ho hq hne z).differentiableAt (by simp)).hasFDerivAt
  have he : (inverse hdim x o q ∘ coordinates hdim x o q) =ᶠ[𝓝 z.val] id :=
    Filter.eventuallyEq_of_mem ((ForestRadialFaceImmersion.isOpen_source hdim x o).mem_nhds z.property)
      (fun w hw ↦ inverse_coordinates hdim x o q ho hq hne ⟨w,hw⟩)
  have h := hd.fderiv
  rw [he.fderiv_eq, fderiv_id] at h
  exact h.symm

include ho hq hne in
theorem differential_bijective : Function.Bijective (fderiv ℝ (coordinates hdim x o q) z.val) := by
  have hi : Function.LeftInverse
      (fderiv ℝ (inverse hdim x o q) (coordinates hdim x o q z.val))
      (fderiv ℝ (coordinates hdim x o q) z.val) := fun v ↦
    congrArg (fun L : Coord r →L[ℝ] Coord r ↦ L v) (differential_leftInverse hdim x o q ho hq hne z)
  have hd : Module.finrank ℝ (Coord r) = Module.finrank ℝ (Face x o q) := by
    rw [finrank_face hdim x o q ho hq hne]
    simp [Coord]
  exact ⟨hi.injective, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hi.injective⟩

def differential : Coord r ≃L[ℝ] Face x o q :=
  ContinuousLinearEquiv.ofBijective (fderiv ℝ (coordinates hdim x o q) z.val)
    (LinearMap.ker_eq_bot.mpr (differential_bijective hdim x o q ho hq hne z).1)
    (LinearMap.range_eq_top.mpr (differential_bijective hdim x o q ho hq hne z).2)

theorem hasStrictFDerivAt_coordinates : HasStrictFDerivAt (coordinates hdim x o q)
    (differential hdim x o q ho hq hne z : Coord r →L[ℝ] Face x o q) z.val := by
  change HasStrictFDerivAt (coordinates hdim x o q) (fderiv ℝ (coordinates hdim x o q) z.val) z.val
  exact (contDiffAt_coordinates hdim x o q ho hq hne z).hasStrictFDerivAt (by simp)

def localChart : OpenPartialHomeomorph (Coord r) (Face x o q) :=
  ((hasStrictFDerivAt_coordinates hdim x o q ho hq hne z).toOpenPartialHomeomorph
    (coordinates hdim x o q)).restrOpen
      (ForestRadialFaceLocalization.source hdim x o) (ForestRadialFaceImmersion.isOpen_source hdim x o)

theorem self_mem_localChart_source : z.val ∈ (localChart hdim x o q ho hq hne z).source :=
  ⟨(hasStrictFDerivAt_coordinates hdim x o q ho hq hne z).mem_toOpenPartialHomeomorph_source, z.property⟩

@[simp] theorem localChart_apply (w : Coord r) : localChart hdim x o q ho hq hne z w = coordinates hdim x o q w := rfl

theorem localChart_source_subset : (localChart hdim x o q ho hq hne z).source ⊆
    ForestRadialFaceLocalization.source hdim x o := Set.inter_subset_right

theorem localChart_symm_eq {y : Face x o q} (hy : y ∈ (localChart hdim x o q ho hq hne z).target) :
    (localChart hdim x o q ho hq hne z).symm y = inverse hdim x o q y := by
  have hw := (localChart hdim x o q ho hq hne z).map_target hy
  have hs := localChart_source_subset hdim x o q ho hq hne z hw
  have h := inverse_coordinates hdim x o q ho hq hne
    ⟨(localChart hdim x o q ho hq hne z).symm y,hs⟩
  change inverse hdim x o q
    (localChart hdim x o q ho hq hne z ((localChart hdim x o q ho hq hne z).symm y)) = _ at h
  rw [(localChart hdim x o q ho hq hne z).right_inv hy] at h
  exact h.symm

end EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestSimpleOverlap
