import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestResolvedCoordinates

/-! The actual proper-real face map is injective on the literal native source
and has precisely the simple real-face dimension. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.RealForestSimpleEmbedding
open Configuration ForestRadialFaceClassification RealForestSimpleCoordinates
open RealForestCoarsePositions (node labelsSet)
open RealForestSimpleCluster (lower upper)
open RealForestResolvedCoordinates
open BoxStokes
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (a b : Fin (n+1)) (ho : RealForestCoarsePositions.IsFixed x o)
  (ha : a ∈ labelsSet x o) (hb : b ∉ labelsSet x o)
  (hne : (boundaryClusterBlock (lower x o) (upper x o)).Nonempty)

include hdim ha hb in
theorem finrank_face :
    Module.finrank ℝ (BoundaryClusterFreeCoordinates.FaceCoordinates b a (labelsSet x o) m) = r := by
  rw [BoundaryClusterFreeCoordinates.finrank_face ha hb]
  dsimp [GraphForms.dimension] at hdim
  omega

theorem native_data_injective (z w : ForestRadialFaceLocalization.source hdim x o)
    (h : ForestRadialFaceDRInverse.data hdim x o z = ForestRadialFaceDRInverse.data hdim x o w) :
    z.val = w.val := by
  have he : ForestRadialFaceImmersion.forward hdim x o z.val =
      ForestRadialFaceImmersion.forward hdim x o w.val := by
    rw [ForestRadialFaceImmersion.forward_data, ForestRadialFaceImmersion.forward_data, h]
  calc
    z.val = ForestRadialFaceImmersion.inverse hdim x o
        (ForestRadialFaceImmersion.forward hdim x o z.val) :=
      (ForestRadialFaceImmersion.inverse_forward hdim x o z).symm
    _ = ForestRadialFaceImmersion.inverse hdim x o
        (ForestRadialFaceImmersion.forward hdim x o w.val) := congrArg _ he
    _ = w.val := ForestRadialFaceImmersion.inverse_forward hdim x o w

include ho ha hb hne in
/-- Injectivity is derived from exact simple/forest full-DR equality and the
actual native inverse; no chart bijection is supplied. -/
theorem coordinates_injective_on : Set.InjOn (coordinates hdim x o a b)
    (ForestRadialFaceLocalization.source hdim x o) := by
  intro z hz w hw he
  let Z : ForestRadialFaceLocalization.source hdim x o := ⟨z,hz⟩
  let W : ForestRadialFaceLocalization.source hdim x o := ⟨w,hw⟩
  have hc : RealForestSimpleCluster.freeDomain hdim x o ho a b ha hb hne Z =
      RealForestSimpleCluster.freeDomain hdim x o ho a b ha hb hne W := by
    apply Subtype.ext
    rw [← coordinates_eq_freeDomain hdim x o a b ho ha hb hne Z,
      ← coordinates_eq_freeDomain hdim x o a b ho ha hb hne W]
    exact congrArg BoundaryClusterFreeCoordinates.faceEmbedding he
  have hd : RealForestSimpleCluster.domain hdim x o ho a b ha hb hne Z =
      RealForestSimpleCluster.domain hdim x o ho a b ha hb hne W := by
    have h := congrArg BoundaryClusterFreeDomain.toDomain hc
    simpa only [RealForestSimpleCluster.freeDomain, BoundaryClusterFreeDomain.toDomain_toFreeDomain] using h
  apply native_data_injective hdim x o Z W
  rw [← insertion_DR_eq_native hdim x o ho a b ha hb hne Z,
    ← insertion_DR_eq_native hdim x o ho a b ha hb hne W, hd]

end EnvelopingIsomorphism.Deformation.Kontsevich.RealForestSimpleEmbedding
