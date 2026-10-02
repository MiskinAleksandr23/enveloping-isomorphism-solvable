import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestSimpleEmbedding
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterFaceDR
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-! Genuine smooth coordinate equivalence between the actual strict native
proper-real face and simple real-cluster coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.RealForestSimpleOverlap
open Configuration ForestRadialFaceClassification RealForestSimpleCoordinates
open RealForestCoarsePositions (node labelsSet)
open RealForestSimpleCluster (lower upper)
open RealForestResolvedCoordinates RealForestSimpleEmbedding
open BoxStokes
open scoped Classical Topology
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (a b : Fin (n+1))

abbrev Face := BoundaryClusterFreeCoordinates.FaceCoordinates b a (labelsSet x o) m

def inverse (y : Face x o a b) : Coord r :=
  ForestRadialFaceImmersion.inverse hdim x o (BoundaryClusterFaceDR.ambient (lower x o) (upper x o) y)

variable (ho : RealForestCoarsePositions.IsFixed x o)
  (ha : a ∈ labelsSet x o) (hb : b ∉ labelsSet x o)
  (hne : (boundaryClusterBlock (lower x o) (upper x o)).Nonempty)
  (z : ForestRadialFaceLocalization.source hdim x o)

include ho ha hb hne in
/-- The smooth simple and native ambient DR maps really agree on the source. -/
theorem ambient_coordinates :
    BoundaryClusterFaceDR.ambient (lower x o) (upper x o) (coordinates hdim x o a b z.val) =
      ForestRadialFaceImmersion.forward hdim x o z.val := by
  rw [BoundaryClusterFaceDR.ambient_eq_data _ _ _
    (coordinates_mem_source hdim x o a b ho ha hb hne z)]
  have hfree : BoundaryClusterFaceDR.sourcePoint (lower x o) (upper x o)
      (coordinates hdim x o a b z.val) (coordinates_mem_source hdim x o a b ho ha hb hne z) =
      RealForestSimpleCluster.freeDomain hdim x o ho a b ha hb hne z :=
    Subtype.ext (coordinates_eq_freeDomain hdim x o a b ho ha hb hne z)
  rw [hfree]
  simp only [RealForestSimpleCluster.freeDomain, BoundaryClusterFreeDomain.toDomain_toFreeDomain]
  rw [insertion_DR_eq_native, ForestRadialFaceImmersion.forward_data]

include ho ha hb hne in
theorem inverse_coordinates : inverse hdim x o a b (coordinates hdim x o a b z.val) = z.val := by
  rw [inverse, ambient_coordinates hdim x o a b ho ha hb hne z]
  exact ForestRadialFaceImmersion.inverse_forward hdim x o z

include ho ha hb hne in
theorem contDiffAt_inverse :
    ContDiffAt ℝ ⊤ (inverse hdim x o a b) (coordinates hdim x o a b z.val) := by
  have h := ForestRadialFaceImmersion.contDiffAt_inverse hdim x o z
  rw [← ambient_coordinates hdim x o a b ho ha hb hne z] at h
  exact h.comp _ (BoundaryClusterFaceDR.contDiffAt_ambient _ _ _
    (coordinates_mem_source hdim x o a b ho ha hb hne z))

include ho ha hb hne in
theorem differential_leftInverse :
    (fderiv ℝ (inverse hdim x o a b) (coordinates hdim x o a b z.val)).comp
      (fderiv ℝ (coordinates hdim x o a b) z.val) = ContinuousLinearMap.id ℝ (Coord r) := by
  have hd := ((contDiffAt_inverse hdim x o a b ho ha hb hne z).differentiableAt (by simp)).hasFDerivAt.comp z.val
    ((contDiffAt_coordinates hdim x o a b ho ha hb z).differentiableAt (by simp)).hasFDerivAt
  have he : (inverse hdim x o a b ∘ coordinates hdim x o a b) =ᶠ[𝓝 z.val] id :=
    Filter.eventuallyEq_of_mem ((ForestRadialFaceImmersion.isOpen_source hdim x o).mem_nhds z.property)
      (fun w hw ↦ inverse_coordinates hdim x o a b ho ha hb hne ⟨w,hw⟩)
  have h := hd.fderiv
  rw [he.fderiv_eq, fderiv_id] at h
  exact h.symm

include ho ha hb hne in
theorem differential_bijective : Function.Bijective (fderiv ℝ (coordinates hdim x o a b) z.val) := by
  have hi : Function.LeftInverse
      (fderiv ℝ (inverse hdim x o a b) (coordinates hdim x o a b z.val))
      (fderiv ℝ (coordinates hdim x o a b) z.val) := fun v ↦
    congrArg (fun L : Coord r →L[ℝ] Coord r ↦ L v) (differential_leftInverse hdim x o a b ho ha hb hne z)
  have hd : Module.finrank ℝ (Coord r) = Module.finrank ℝ (Face x o a b) := by
    rw [finrank_face hdim x o a b ha hb]
    simp [Coord]
  exact ⟨hi.injective, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hi.injective⟩

def differential : Coord r ≃L[ℝ] Face x o a b :=
  ContinuousLinearEquiv.ofBijective (fderiv ℝ (coordinates hdim x o a b) z.val)
    (LinearMap.ker_eq_bot.mpr (differential_bijective hdim x o a b ho ha hb hne z).1)
    (LinearMap.range_eq_top.mpr (differential_bijective hdim x o a b ho ha hb hne z).2)

theorem hasStrictFDerivAt_coordinates : HasStrictFDerivAt (coordinates hdim x o a b)
    (differential hdim x o a b ho ha hb hne z : Coord r →L[ℝ] Face x o a b) z.val := by
  change HasStrictFDerivAt (coordinates hdim x o a b) (fderiv ℝ (coordinates hdim x o a b) z.val) z.val
  exact (contDiffAt_coordinates hdim x o a b ho ha hb z).hasStrictFDerivAt (by simp)

/-- The actual inverse-function theorem chart is restricted to the literal
native radial source; no chart or Jacobian premise is supplied. -/
def localChart : OpenPartialHomeomorph (Coord r) (Face x o a b) :=
  ((hasStrictFDerivAt_coordinates hdim x o a b ho ha hb hne z).toOpenPartialHomeomorph
    (coordinates hdim x o a b)).restrOpen
      (ForestRadialFaceLocalization.source hdim x o) (ForestRadialFaceImmersion.isOpen_source hdim x o)

theorem self_mem_localChart_source : z.val ∈ (localChart hdim x o a b ho ha hb hne z).source :=
  ⟨(hasStrictFDerivAt_coordinates hdim x o a b ho ha hb hne z).mem_toOpenPartialHomeomorph_source, z.property⟩

@[simp] theorem localChart_apply (w : Coord r) :
    localChart hdim x o a b ho ha hb hne z w = coordinates hdim x o a b w := rfl

theorem localChart_source_subset : (localChart hdim x o a b ho ha hb hne z).source ⊆
    ForestRadialFaceLocalization.source hdim x o := Set.inter_subset_right

/-- Its inverse is the explicit smooth native decoder applied to genuine
simple-face direction and ratio coordinates. -/
theorem localChart_symm_eq {y : Face x o a b} (hy : y ∈ (localChart hdim x o a b ho ha hb hne z).target) :
    (localChart hdim x o a b ho ha hb hne z).symm y = inverse hdim x o a b y := by
  have hw := (localChart hdim x o a b ho ha hb hne z).map_target hy
  have hs := localChart_source_subset hdim x o a b ho ha hb hne z hw
  have h := inverse_coordinates hdim x o a b ho ha hb hne
    ⟨(localChart hdim x o a b ho ha hb hne z).symm y,hs⟩
  change inverse hdim x o a b
    (localChart hdim x o a b ho ha hb hne z ((localChart hdim x o a b ho ha hb hne z).symm y)) = _ at h
  rw [(localChart hdim x o a b ho ha hb hne z).right_inv hy] at h
  exact h.symm

end EnvelopingIsomorphism.Deformation.Kontsevich.RealForestSimpleOverlap
