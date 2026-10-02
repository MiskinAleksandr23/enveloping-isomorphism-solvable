import EnvelopingIsomorphism.Deformation.Kontsevich.PureForestSimpleCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryFaceDR
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-! Actual smooth local coordinate equivalence for a strict pure-boundary
forest face, with explicit full-DR inverse and no assumed Jacobian law. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PureForestSimpleOverlap
open Configuration ForestRadialFaceClassification PureForestSimpleCoordinates
open PureForestSimpleCluster (lower upper)
open BoxStokes
open scoped Classical Topology
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : ForestRadialFaceClassification.Orbit 0 x) (a b : Fin m)

abbrev Face := PureBoundaryClusterForms.Face n (boundaryClusterBlock (lower x o) (upper x o)) a b

def inverse (y : Face x o a b) : Coord r :=
  ForestRadialFaceImmersion.inverse hdim x o (PureBoundaryFaceDR.ambient (lower x o) (upper x o) a b y)

variable (ho : kind 0 x o = .pureBoundary)
  (hl : a.val = (lower x o).val) (hu : b.val + 1 = (upper x o).val) (hab : a < b)
  (z : ForestRadialFaceLocalization.source hdim x o)

include ho hl hu hab in
theorem ambient_coordinates :
    PureBoundaryFaceDR.ambient (lower x o) (upper x o) a b (coordinates hdim x o a b z.val) =
      ForestRadialFaceImmersion.forward hdim x o z.val := by
  rw [coordinates_eq_datum hdim x o a b ho hl hu hab z, PureBoundaryFaceDR.ambient_data]
  change CompactDRCoordinates.dataEmbedding
    (projectDR (PureForestSimpleCluster.domain hdim x o ho a b hl hu hab z).insertion.val) = _
  rw [PureForestResolvedCoordinates.insertion_DR_eq_native, ForestRadialFaceImmersion.forward_data]

include ho hl hu hab in
theorem contDiffAt_inverse : ContDiffAt ℝ ⊤ (inverse hdim x o a b) (coordinates hdim x o a b z.val) := by
  have h := ForestRadialFaceImmersion.contDiffAt_inverse hdim x o z
  rw [← ambient_coordinates hdim x o a b ho hl hu hab z] at h
  apply h.comp
  rw [coordinates_eq_datum hdim x o a b ho hl hu hab z]
  exact PureBoundaryFaceDR.contDiffAt_ambient_data _ _ _ _ _

include hdim ho hl hu hab in
theorem finrank_face : Module.finrank ℝ (Face x o a b) = r := by
  rw [PureBoundaryClusterForms.finrank_face _ a b
    (PureForestSimpleCluster.left_mem x o a b hl hu hab)
    (PureForestSimpleCluster.right_mem x o a b hl hu hab) hab.ne]
  change n * 2 + m = r + 1 at hdim
  omega

include ho hl hu hab in
theorem inverse_coordinates : inverse hdim x o a b (coordinates hdim x o a b z.val) = z.val := by
  rw [inverse, ambient_coordinates hdim x o a b ho hl hu hab z]
  exact ForestRadialFaceImmersion.inverse_forward hdim x o z

include ho hl hu hab in
theorem differential_leftInverse :
    (fderiv ℝ (inverse hdim x o a b) (coordinates hdim x o a b z.val)).comp
      (fderiv ℝ (coordinates hdim x o a b) z.val) = ContinuousLinearMap.id ℝ (Coord r) := by
  have hd := ((contDiffAt_inverse hdim x o a b ho hl hu hab z).differentiableAt (by simp)).hasFDerivAt.comp z.val
    ((contDiffAt_coordinates hdim x o a b ho hl hu hab z).differentiableAt (by simp)).hasFDerivAt
  have he : (inverse hdim x o a b ∘ coordinates hdim x o a b) =ᶠ[𝓝 z.val] id :=
    Filter.eventuallyEq_of_mem ((ForestRadialFaceImmersion.isOpen_source hdim x o).mem_nhds z.property)
      (fun w hw ↦ inverse_coordinates hdim x o a b ho hl hu hab ⟨w,hw⟩)
  have h := hd.fderiv
  rw [he.fderiv_eq, fderiv_id] at h
  exact h.symm

include ho hl hu hab in
theorem differential_bijective : Function.Bijective (fderiv ℝ (coordinates hdim x o a b) z.val) := by
  have hi : Function.LeftInverse
      (fderiv ℝ (inverse hdim x o a b) (coordinates hdim x o a b z.val))
      (fderiv ℝ (coordinates hdim x o a b) z.val) := fun v ↦
    congrArg (fun L : Coord r →L[ℝ] Coord r ↦ L v) (differential_leftInverse hdim x o a b ho hl hu hab z)
  have hd : Module.finrank ℝ (Coord r) = Module.finrank ℝ (Face x o a b) := by
    rw [finrank_face hdim x o a b ho hl hu hab]
    simp [Coord]
  exact ⟨hi.injective, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hi.injective⟩

def differential : Coord r ≃L[ℝ] Face x o a b :=
  ContinuousLinearEquiv.ofBijective (fderiv ℝ (coordinates hdim x o a b) z.val)
    (LinearMap.ker_eq_bot.mpr (differential_bijective hdim x o a b ho hl hu hab z).1)
    (LinearMap.range_eq_top.mpr (differential_bijective hdim x o a b ho hl hu hab z).2)

theorem hasStrictFDerivAt_coordinates : HasStrictFDerivAt (coordinates hdim x o a b)
    (differential hdim x o a b ho hl hu hab z : Coord r →L[ℝ] Face x o a b) z.val := by
  change HasStrictFDerivAt (coordinates hdim x o a b) (fderiv ℝ (coordinates hdim x o a b) z.val) z.val
  exact (contDiffAt_coordinates hdim x o a b ho hl hu hab z).hasStrictFDerivAt (by simp)

def localChart : OpenPartialHomeomorph (Coord r) (Face x o a b) :=
  ((hasStrictFDerivAt_coordinates hdim x o a b ho hl hu hab z).toOpenPartialHomeomorph
    (coordinates hdim x o a b)).restrOpen
      (ForestRadialFaceLocalization.source hdim x o) (ForestRadialFaceImmersion.isOpen_source hdim x o)

theorem self_mem_localChart_source : z.val ∈ (localChart hdim x o a b ho hl hu hab z).source :=
  ⟨(hasStrictFDerivAt_coordinates hdim x o a b ho hl hu hab z).mem_toOpenPartialHomeomorph_source, z.property⟩

@[simp] theorem localChart_apply (w : Coord r) : localChart hdim x o a b ho hl hu hab z w = coordinates hdim x o a b w := rfl

theorem localChart_source_subset : (localChart hdim x o a b ho hl hu hab z).source ⊆
    ForestRadialFaceLocalization.source hdim x o := Set.inter_subset_right

theorem localChart_symm_eq {y : Face x o a b} (hy : y ∈ (localChart hdim x o a b ho hl hu hab z).target) :
    (localChart hdim x o a b ho hl hu hab z).symm y = inverse hdim x o a b y := by
  have hw := (localChart hdim x o a b ho hl hu hab z).map_target hy
  have hs := localChart_source_subset hdim x o a b ho hl hu hab z hw
  have h := inverse_coordinates hdim x o a b ho hl hu hab
    ⟨(localChart hdim x o a b ho hl hu hab z).symm y,hs⟩
  change inverse hdim x o a b
    (localChart hdim x o a b ho hl hu hab z ((localChart hdim x o a b ho hl hu hab z).symm y)) = _ at h
  rw [(localChart hdim x o a b ho hl hu hab z).right_inv hy] at h
  exact h.symm

end EnvelopingIsomorphism.Deformation.Kontsevich.PureForestSimpleOverlap
