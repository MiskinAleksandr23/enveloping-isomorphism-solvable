import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterFreeCoordinateEquiv
import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterCoordinateModel
import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterCoverage
import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterAngularChart

/-!
Genuine local half-space charts at pure boundary-cluster faces. Their open image
comes from the proved actual reconstruction, compact-coordinate embedding, and
coverage theorem. The scaled position coordinates are the explicit smooth
polynomials of the free model.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterFreeDomain

open Topology Set Configuration

variable {n m : ℕ} {i : Fin n} {l u : Fin (m + 1)} {a b : Fin m}

def toCompactification (x : PureBoundaryClusterFreeDomain i m l u a b) : Compactification i m :=
  x.toDomain.insertion

theorem isEmbedding_toCompactification :
    IsEmbedding (toCompactification : PureBoundaryClusterFreeDomain i m l u a b → Compactification i m) :=
  PureBoundaryClusterDomain.isEmbedding_insertion.comp pureBoundaryClusterFreeHomeomorph.isEmbedding

theorem isLocalHomeomorphOn_toCompactification :
    IsLocalHomeomorphOn (toCompactification : PureBoundaryClusterFreeDomain i m l u a b → Compactification i m)
      {x | x.val.radius = 0} := by
  apply (isLocalHomeomorphOn_interior_range PureBoundaryClusterDomain.isEmbedding_insertion).comp
    pureBoundaryClusterFreeHomeomorph.isLocalHomeomorph.isLocalHomeomorphOn
  intro x hx
  apply PureBoundaryClusterDomain.mem_interior_range_insertion x.toDomain
  simpa only [toDomain_scale, Set.mem_setOf_eq] using hx

/-- A genuine open partial homeomorphism at each admissible zero-radius free point. -/
theorem exists_chart_at_scale_zero (x : PureBoundaryClusterFreeDomain i m l u a b) (hx : x.val.radius = 0) :
    ∃ e : OpenPartialHomeomorph (PureBoundaryClusterFreeDomain i m l u a b) (Compactification i m),
      x ∈ e.source ∧ (toCompactification : PureBoundaryClusterFreeDomain i m l u a b → _) = e :=
  isLocalHomeomorphOn_toCompactification x hx

/-- The free charts cover every point of the native pure boundary-cluster face. -/
theorem exists_chart_for_domain_face (x : PureBoundaryClusterDomain i m l u a b) (hx : x.scale = 0) :
    ∃ y : PureBoundaryClusterFreeDomain i m l u a b,
      ∃ e : OpenPartialHomeomorph (PureBoundaryClusterFreeDomain i m l u a b) (Compactification i m),
        y ∈ e.source ∧ e y = x.insertion ∧
          (toCompactification : PureBoundaryClusterFreeDomain i m l u a b → _) = e := by
  let y := x.toFreeDomain
  have hy : y.val.radius = 0 := hx
  obtain ⟨e, he, hmap⟩ := exists_chart_at_scale_zero y hy
  refine ⟨y, e, he, ?_, hmap⟩
  rw [← hmap, toCompactification]
  exact congrArg PureBoundaryClusterDomain.insertion (toDomain_toFreeDomain x)

/-- Interior positions of the compact insertion are the actual free coordinates. -/
@[simp] theorem toCompactification_interior_position (x : PureBoundaryClusterFreeDomain i m l u a b)
    (j : Fin n) : x.toCompactification.val.1 (Sum.inl j) = (x.val.interior j : OnePoint ℂ) := by
  change (((x.datum.interior j : ℂ) + (x.val.radius : ℂ) * 0 : ℂ) : OnePoint ℂ) = _
  simp only [mul_zero, add_zero, datum_interior]

/-- Boundary positions are exactly the smooth scaled boundary polynomials. -/
@[simp] theorem toCompactification_boundary_position (x : PureBoundaryClusterFreeDomain i m l u a b)
    (j : Fin m) : x.toCompactification.val.1 (Sum.inr j) =
      ((x.val.scaledBoundary l u j : ℂ) : OnePoint ℂ) := by
  change (((x.datum.boundaryBase j : ℂ) + (x.val.radius : ℂ) *
    (x.datum.boundaryVelocity j : ℂ) : ℂ) : OnePoint ℂ) = _
  rw [datum_boundaryBase, datum_boundaryVelocity]
  simp only [PureBoundaryClusterFreeCoordinates.scaledBoundary, Complex.ofReal_add, Complex.ofReal_mul]

end EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterFreeDomain
