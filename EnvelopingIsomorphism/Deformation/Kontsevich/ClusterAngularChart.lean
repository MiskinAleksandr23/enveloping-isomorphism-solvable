import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterAngularDomain
import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterCoordinateModel
import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorClusterLocalCoverage

/-!
# Actual local angular/radial charts in the compactification

The domain is the proved open subset of a single radial half-space. Near its
scale-zero points, the angular parameter map is a local homeomorphism into the
actual compactification, using the previously proved local image coverage.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Topology Set

theorem isLocalHomeomorphOn_interior_range {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsEmbedding f) :
    IsLocalHomeomorphOn f (f ⁻¹' interior (Set.range f)) := by
  apply (isLocalHomeomorphOn_iff_isOpenEmbedding_restrict (f ⁻¹' interior (Set.range f))).mpr
  intro x hx
  let U := f ⁻¹' interior (Set.range f)
  have hU : IsOpen U := isOpen_interior.preimage hf.continuous
  refine ⟨U, hU.mem_nhds hx, hf.comp IsEmbedding.subtypeVal, ?_⟩
  rw [Set.range_restrict, Set.image_preimage_eq_inter_range, inter_eq_left.mpr interior_subset]
  exact isOpen_interior

namespace ClusterAngularDomain

variable {n m : ℕ} {i a b : Fin n} {S : Finset (Fin n)}

def toCompactification (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hanchor : i ∈ S → a = i)
    (x : ClusterAngularDomain i a b S m) : Compactification i m :=
  (toSlice ha hb hba hanchor x).insertion

theorem isLocalHomeomorphOn_toCompactification (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) :
    IsLocalHomeomorphOn (toCompactification ha hb hba hanchor)
      {x : ClusterAngularDomain i a b S m | x.val.toFree.radius = 0} := by
  apply (isLocalHomeomorphOn_interior_range
    (NormalizedInteriorClusterSlice.isEmbedding_insertion ha hb hba)).comp
    (isLocalHomeomorph_toSlice ha hb hba hanchor).isLocalHomeomorphOn
  intro x hx
  apply NormalizedInteriorClusterSlice.mem_interior_range_insertion _ ha hb hba
  change (clusterFreeHomeomorph ha hb hba hanchor (toFreeDomain x)).val.scale = 0
  rw [clusterFreeHomeomorph_apply, ClusterFreeDomain.toSlice_scale]
  exact hx

/-- Each scale-zero angular parameter has a genuine open partial homeomorphism
chart into the compactification, without postulating image openness. -/
theorem exists_chart_at_scale_zero (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) (x : ClusterAngularDomain i a b S m)
    (hx : x.val.toFree.radius = 0) :
    ∃ e : OpenPartialHomeomorph (ClusterAngularDomain i a b S m) (Compactification i m),
      x ∈ e.source ∧ toCompactification ha hb hba hanchor = e :=
  isLocalHomeomorphOn_toCompactification ha hb hba hanchor x hx

/-- Every point of the normalized simple-cluster face has one of these genuine angular/radial charts. -/
theorem exists_chart_for_slice_face (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) (x : NormalizedInteriorClusterSlice i m S a b)
    (hx : x.val.scale = 0) :
    ∃ y : ClusterAngularDomain i a b S m,
      ∃ e : OpenPartialHomeomorph (ClusterAngularDomain i a b S m) (Compactification i m),
        y ∈ e.source ∧ e y = x.insertion ∧ toCompactification ha hb hba hanchor = e := by
  obtain ⟨y, hy⟩ := surjective_toSlice ha hb hba hanchor x
  have hr : y.val.toFree.radius = 0 := by
    have hscale : (toSlice ha hb hba hanchor y).val.scale = y.val.toFree.radius := by
      rw [toSlice, clusterFreeHomeomorph_apply, ClusterFreeDomain.toSlice_scale]
      rfl
    rw [← hscale, hy, hx]
  obtain ⟨e, he, hmap⟩ := exists_chart_at_scale_zero ha hb hba hanchor y hr
  refine ⟨y, e, he, ?_, hmap⟩
  rw [← hmap]
  exact congrArg NormalizedInteriorClusterSlice.insertion hy

end ClusterAngularDomain

end EnvelopingIsomorphism.Deformation.Kontsevich
