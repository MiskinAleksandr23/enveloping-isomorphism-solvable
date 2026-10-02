import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterFreeCoordinateEquiv
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterCoordinateModel
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterLocalCoverage
import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterAngularChart

/-! Genuine local half-space charts at finite real-cluster faces. The open
image follows from the already proved geometric coverage, not an assumption. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterFreeDomain

open Topology Set

variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

def toCompactification (x : BoundaryClusterFreeDomain i a S m l u) : Compactification i m :=
  x.toDomain.insertion

theorem isEmbedding_toCompactification :
    IsEmbedding (toCompactification : BoundaryClusterFreeDomain i a S m l u → Compactification i m) :=
  BoundaryClusterDomain.isEmbedding_insertion.comp boundaryClusterFreeHomeomorph.isEmbedding

theorem isLocalHomeomorphOn_toCompactification :
    IsLocalHomeomorphOn (toCompactification : BoundaryClusterFreeDomain i a S m l u → Compactification i m)
      {x | x.val.radius = 0} := by
  apply (isLocalHomeomorphOn_interior_range BoundaryClusterDomain.isEmbedding_insertion).comp
    boundaryClusterFreeHomeomorph.isLocalHomeomorph.isLocalHomeomorphOn
  intro x hx
  apply BoundaryClusterDomain.mem_interior_range_insertion x.toDomain
  simpa only [toDomain_scale, Set.mem_setOf_eq] using hx

/-- A true open partial homeomorphism at every admissible zero-radius free parameter. -/
theorem exists_chart_at_scale_zero (x : BoundaryClusterFreeDomain i a S m l u) (hx : x.val.radius = 0) :
    ∃ e : OpenPartialHomeomorph (BoundaryClusterFreeDomain i a S m l u) (Compactification i m),
      x ∈ e.source ∧ (toCompactification : BoundaryClusterFreeDomain i a S m l u → _) = e :=
  isLocalHomeomorphOn_toCompactification x hx

/-- These half-space charts reach every point of the actual simple real-cluster face. -/
theorem exists_chart_for_domain_face (x : BoundaryClusterDomain i a m S l u) (hx : x.scale = 0) :
    ∃ y : BoundaryClusterFreeDomain i a S m l u,
      ∃ e : OpenPartialHomeomorph (BoundaryClusterFreeDomain i a S m l u) (Compactification i m),
        y ∈ e.source ∧ e y = x.insertion ∧ (toCompactification : BoundaryClusterFreeDomain i a S m l u → _) = e := by
  let y := x.toFreeDomain
  have hy : y.val.radius = 0 := hx
  obtain ⟨e, he, hmap⟩ := exists_chart_at_scale_zero y hy
  refine ⟨y, e, he, ?_, hmap⟩
  rw [← hmap, toCompactification]
  exact congrArg BoundaryClusterDomain.insertion (toDomain_toFreeDomain x)

end EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterFreeDomain
