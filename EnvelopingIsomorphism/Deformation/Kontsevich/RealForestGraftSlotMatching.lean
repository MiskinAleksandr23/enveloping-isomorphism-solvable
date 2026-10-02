import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestExplicitTransfer
import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestOrderedSlotSign

/-! Separating the actual graph-row sign from the geometric chamber sign,
without discarding either permutation in the genuine graft formula. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.RealForestGraftSlotMatching
open scoped Classical BigOperators
open BoundaryGraphFaceFactorization BoundaryGraphOrderedCoordinates BoundaryGraphOrderedIntegrals
open BoundaryGraphGraftReconstruction BoundaryGraphValenceSelection BoundaryGraphCanonicalFibreMatching
open BoundaryGraphNativeTransport
open KontsevichGraph.General
variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m+1)} {q : Fin n → ℕ}
  (Γ : Graph q m) (ha : a ∈ S) (hi : i ∉ S)
  (order : Fin (shapeDegree a S l u + coarseDegree i S l u) ≃ KontsevichGraph.General.Edge q)
  (hcount : Fintype.card {j // (graphEdges Γ order j).1 ∈ S} = shapeDegree a S l u)

/-- Only the actual edge block and actual extracted graph row permutations. -/
def edgeOrderingSign : ℝ :=
  (Equiv.Perm.sign (edgeBlockPermutation (graphEdges Γ order) S hcount).symm : ℝ) *
    (outerRowPermutation Γ ha hi order hcount).sign *
    (innerRowPermutation Γ ha hi order hcount).sign

theorem fibreSign_eq_nativeOrdered_mul_edgeOrderingSign (hlu : l < u) :
    fibreSign Γ ha hi order hcount hlu =
      (Equiv.Perm.sign (nativeOrderedPermutation (i := i) (a := a) (S := S) (le_of_lt hlu)) : ℝ) *
        edgeOrderingSign Γ ha hi order hcount := by
  rw [fibreSign, orderedFaceSign, nativeOrderedPermutation_sign]
  unfold edgeOrderingSign
  push_cast
  ring

/-- The actual radial-first normalized graft integral with all graph-row
signs retained, ready for the finite numerical chamber-slot computation. -/
theorem normalized_graft_eq_coordinate_signed
    (hlu : l < u)
    (hn : ∀ e : KontsevichGraph.General.Edge q, e.1 ∈ S → boundaryClusterCollapses S l u (Sum.inl (Γ.target e)))
    (hd : (orderedGraph Γ ha hi hlu).CoarseDistinct (centerSlot (le_of_lt hlu))) :
    (∏ v : Fin n, ((q v).factorial : ℝ)⁻¹) *
      ((2 * Real.pi) ^ (shapeDegree a S l u + coarseDegree i S l u))⁻¹ *
      BoundaryGraphRadiusFirstTransport.outwardRadiusFirstIntegral (graphEdges Γ order) =
    -(Equiv.Perm.sign (nativeOrderedPermutation (i := i) (a := a) (S := S) (le_of_lt hlu)) : ℝ) *
      edgeOrderingSign Γ ha hi order hcount *
      GraphGeneralWeightedGraft.graftProfile (centerSlot (le_of_lt hlu))
        (outerCoefficient Γ ha hi order hcount) (innerCoefficient Γ ha hi order hcount hlu)
        (orderedGraph Γ ha hi hlu) := by
  rw [BoundaryGraphRadiusFirstTransport.normalized_radiusFirst_integral_eq_signed_graftProfile Γ ha hi order hcount hlu hn hd,
    fibreSign_eq_nativeOrdered_mul_edgeOrderingSign]
  ring

end EnvelopingIsomorphism.Deformation.Kontsevich.RealForestGraftSlotMatching

namespace EnvelopingIsomorphism.Deformation.Kontsevich.RealForestGraftSlotMatching
open scoped Classical BigOperators
open BoundaryGraphFaceFactorization BoundaryGraphOrderedCoordinates BoundaryGraphOrderedIntegrals
open BoundaryGraphGraftReconstruction BoundaryGraphValenceSelection BoundaryGraphCanonicalFibreMatching
open KontsevichGraph.General
variable {n : ℕ} {i a : Fin n} {S : Finset (Fin n)} {q : Fin n → ℕ}

/-- In the first ordered chamber the radial outward sign cancels the
actual odd scalar permutation, retaining every graph-edge ordering sign. -/
theorem normalized_graft_slotZero
    (Γ : Graph q 3) (ha : a ∈ S) (hi : i ∉ S)
    (order : Fin (shapeDegree a S (0 : Fin 4) 2 + coarseDegree i S (0 : Fin 4) 2) ≃ KontsevichGraph.General.Edge q)
    (hcount : Fintype.card {j // (graphEdges Γ order j).1 ∈ S} = shapeDegree a S (0 : Fin 4) 2)
    (hn : ∀ e : KontsevichGraph.General.Edge q, e.1 ∈ S → boundaryClusterCollapses S (0 : Fin 4) 2 (Sum.inl (Γ.target e)))
    (hd : (orderedGraph Γ ha hi (show (0 : Fin 4) < 2 by decide)).CoarseDistinct
      (centerSlot (show (0 : Fin 4) ≤ 2 by decide))) :
    (∏ v : Fin n, ((q v).factorial : ℝ)⁻¹) *
      ((2 * Real.pi) ^ (shapeDegree a S (0 : Fin 4) 2 + coarseDegree i S (0 : Fin 4) 2))⁻¹ *
      BoundaryGraphRadiusFirstTransport.outwardRadiusFirstIntegral (graphEdges Γ order) =
    edgeOrderingSign Γ ha hi order hcount *
      GraphGeneralWeightedGraft.graftProfile (centerSlot (show (0 : Fin 4) ≤ 2 by decide))
        (outerCoefficient Γ ha hi order hcount)
        (innerCoefficient Γ ha hi order hcount (show (0 : Fin 4) < 2 by decide))
        (orderedGraph Γ ha hi (show (0 : Fin 4) < 2 by decide)) := by
  simpa [RealForestOrderedSlotSign.nativeOrderedPermutation_slotZero] using
    normalized_graft_eq_coordinate_signed Γ ha hi order hcount (show (0 : Fin 4) < 2 by decide) hn hd

/-- In the second ordered chamber the actual scalar permutation is even,
so the radial outward sign remains negative. -/
theorem normalized_graft_slotOne
    (Γ : Graph q 3) (ha : a ∈ S) (hi : i ∉ S)
    (order : Fin (shapeDegree a S (1 : Fin 4) 3 + coarseDegree i S (1 : Fin 4) 3) ≃ KontsevichGraph.General.Edge q)
    (hcount : Fintype.card {j // (graphEdges Γ order j).1 ∈ S} = shapeDegree a S (1 : Fin 4) 3)
    (hn : ∀ e : KontsevichGraph.General.Edge q, e.1 ∈ S → boundaryClusterCollapses S (1 : Fin 4) 3 (Sum.inl (Γ.target e)))
    (hd : (orderedGraph Γ ha hi (show (1 : Fin 4) < 3 by decide)).CoarseDistinct
      (centerSlot (show (1 : Fin 4) ≤ 3 by decide))) :
    (∏ v : Fin n, ((q v).factorial : ℝ)⁻¹) *
      ((2 * Real.pi) ^ (shapeDegree a S (1 : Fin 4) 3 + coarseDegree i S (1 : Fin 4) 3))⁻¹ *
      BoundaryGraphRadiusFirstTransport.outwardRadiusFirstIntegral (graphEdges Γ order) =
    -(edgeOrderingSign Γ ha hi order hcount) *
      GraphGeneralWeightedGraft.graftProfile (centerSlot (show (1 : Fin 4) ≤ 3 by decide))
        (outerCoefficient Γ ha hi order hcount)
        (innerCoefficient Γ ha hi order hcount (show (1 : Fin 4) < 3 by decide))
        (orderedGraph Γ ha hi (show (1 : Fin 4) < 3 by decide)) := by
  simpa [RealForestOrderedSlotSign.nativeOrderedPermutation_slotOne] using
    normalized_graft_eq_coordinate_signed Γ ha hi order hcount (show (1 : Fin 4) < 3 by decide) hn hd

end EnvelopingIsomorphism.Deformation.Kontsevich.RealForestGraftSlotMatching
