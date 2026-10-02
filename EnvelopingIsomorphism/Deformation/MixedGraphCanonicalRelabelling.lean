import EnvelopingIsomorphism.Deformation.MixedGraphBoundaryProfiles

/-! Actual canonical scalar weights under mixed relabelling. In the two-odd
quotient carrier it is the signed placement weight that is invariant. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedGraphBoundaryProfiles
open scoped BigOperators Classical
open KontsevichGraph.General MixedGraphProfileCarrier MixedGraphAveraging
open MixedGraphCorrectionProfiles
variable {n : ℕ}

/-- Relabel both exceptional quotient vertices, retaining their distinctness. -/
def correctionPlacementEquiv (σ : Equiv.Perm (Fin (n + 2))) : Equiv.Perm (Placement n) :=
  Equiv.sigmaCongr σ (fun _ => Equiv.subtypeEquiv σ (fun _ => σ.injective.ne_iff.symm))

/-- Actual relabelling of a quotient with its vector and trivector placements. -/
def correctionGraphEquiv (σ : Equiv.Perm (Fin (n + 2))) : Equiv.Perm (CorrectionGraph n) :=
  Equiv.sigmaCongr (correctionPlacementEquiv σ)
    (fun p => Graph.twoOddGraphEquiv p.1 p.2 σ 2)

variable {k : Type*} [Field k] [Algebra ℝ k]

/-- One exceptional odd vertex introduces no internal relabelling sign. -/
theorem canonicalVelocityWeight_internalGraphEquiv
    (σ : Equiv.Perm (Fin (n + 1))) (Γ : VectorGraph n 1) :
    canonicalVelocityWeight (k := k) (internalGraphEquiv σ 1 Γ) =
      canonicalVelocityWeight Γ := by
  unfold canonicalVelocityWeight
  congr 1
  exact Kontsevich.GeometricWeights.canonicalEffectiveWeight_oneExceptionalGraphEquiv
    1 Γ.vertex σ Γ.graph _ _

/-- Fixed X,Q ordering compensates the actual two-odd weight sign over any
real algebra; every quotient placement remains present in this identity. -/
theorem signed_canonicalQuotientWeight_correctionGraphEquiv
    (σ : Equiv.Perm (Fin (n + 2))) (Γ : CorrectionGraph n) :
    placementSign (k := k) (correctionGraphEquiv σ Γ).1 *
        canonicalQuotientWeight (correctionGraphEquiv σ Γ) =
      placementSign Γ.1 * canonicalQuotientWeight Γ := by
  have h := signed_canonicalEffectiveWeight_twoOddGraphEquiv Γ.1.1 Γ.1.2
    Γ.1.2.property σ Γ.2 (edgeCount Γ.1) (edgeCount (correctionPlacementEquiv σ Γ.1))
  have hm := congrArg (algebraMap ℝ k) h
  change (twoOddPlacementSign (σ Γ.1.1) (σ Γ.1.2) : k) *
      algebraMap ℝ k (Kontsevich.GeometricWeights.canonicalEffectiveWeight
        (Graph.twoOddGraphEquiv Γ.1.1 Γ.1.2 σ 2 Γ.2) _) =
    (twoOddPlacementSign Γ.1.1 Γ.1.2 : k) *
      algebraMap ℝ k (Kontsevich.GeometricWeights.canonicalEffectiveWeight Γ.2 _)
  simpa only [map_mul, map_intCast] using hm


end EnvelopingIsomorphism.Deformation.MixedGraphBoundaryProfiles
