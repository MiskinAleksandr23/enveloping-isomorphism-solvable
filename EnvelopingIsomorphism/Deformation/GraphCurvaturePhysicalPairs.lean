import EnvelopingIsomorphism.Deformation.GraphCurvatureInternalRelabelling
import EnvelopingIsomorphism.Deformation.GraphCurvatureExtractedCoefficient
import EnvelopingIsomorphism.Deformation.GeneralGraphSplitPairRelabelling

/-! The complete main curvature boundary profile as a sum of literal extracted
raw weights over physical unordered pairs. All internal/outgoing label
multiplicities, orientation signs and MC factorials are proved and cancelled. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.GraphCurvaturePhysicalPairs
open KontsevichGraph.General KontsevichGraph.General.Graph
open UniformBinaryGraphs GraphCurvatureProfiles GraphCurvatureOutgoingAverage BinaryGraphAveraging
open GraphCurvatureInternalRelabelling GraphCurvatureExtractedCoefficient
open GraphCurvatureLabelCounting GraphLabelledClusterCounting
open scoped Classical BigOperators
variable {n : ℕ}

/-- Actual pair-preserving relabellings preserve the extracted raw quotient
coefficient. Root movement and child exchange are constructed from the given permutation. -/
theorem coefficient_pairRelabelling (i j : Fin (n + 1)) (π : Equiv.Perm (Fin (n + 2)))
    (hπ : ∀ v, π v ∈ childPair j ↔ v ∈ childPair i) (H : BinaryGraph (n + 2) 3) :
    coefficient j (H.permuteInternal π) = coefficient i H := by
  obtain ⟨σ,hr,δ,hδ⟩ := GeneralGraphSplitPairRelabelling.exists_quotient_children i j π hπ
  subst j
  rw [coefficient_eq_average, coefficient_eq_average]
  have h := outgoing_pairProfile_internal i σ δ H
  rw [hδ] at h
  rw [h]

/-- Choose one actual labelling for each unordered physical pair. All choices
are proved immaterial by the next theorem. -/
def representative (T : PhysicalPair n) : PairLabelFiber T := by
  let r := clusterRepresentative (childPair (0 : Fin (n + 1)))
    ⟨T.val,T.property.trans (card_childPair 0).symm⟩
  exact ⟨(0,r.val),(movedPair_eq_iff 0 r.val T).mpr r.property⟩

/-- The finite physical-pair coefficient consists solely of the actual
extracted raw quotient weight (or zero outside the admissible class). -/
def physicalCoefficient (H : BinaryGraph (n + 2) 3) (T : PhysicalPair n) : ℝ :=
  coefficient (representative T).val.1 (H.permuteInternal (representative T).val.2.symm)

/-- Any two original labellings of the same physical pair give exactly the
same coefficient. No scalar invariance premise is supplied. -/
theorem coefficient_same_pair (H : BinaryGraph (n + 2) 3) (T : PhysicalPair n)
    (D E : PairLabelFiber T) :
    coefficient D.val.1 (H.permuteInternal D.val.2.symm) =
      coefficient E.val.1 (H.permuteInternal E.val.2.symm) := by
  let π := D.val.2.trans E.val.2.symm
  have hd := (movedPair_eq_iff D.val.1 D.val.2 T).mp D.property
  have he := (movedPair_eq_iff E.val.1 E.val.2 T).mp E.property
  have hp : ∀ v, π v ∈ childPair E.val.1 ↔ v ∈ childPair D.val.1 := by
    intro v
    have hh := he (E.val.2.symm (D.val.2 v))
    simp only [Equiv.apply_symm_apply] at hh
    exact hh.symm.trans (hd v)
  have h := coefficient_pairRelabelling D.val.1 E.val.1 π hp (H.permuteInternal D.val.2.symm)
  have hcomp : D.val.2.symm.trans π = E.val.2.symm := by
    apply Equiv.ext
    intro v
    simp [π]
  rw [permuteInternal_trans, hcomp] at h
  exact h.symm

theorem coefficient_eq_physical (H : BinaryGraph (n + 2) 3) (T : PhysicalPair n)
    (D : PairLabelFiber T) :
    coefficient D.val.1 (H.permuteInternal D.val.2.symm) = physicalCoefficient H T :=
  coefficient_same_pair H T D (representative T)

/-- Native face matching may use any actual labelling of its pair. The value
is the literal signed raw quotient weight in that labelling. -/
theorem physicalCoefficient_eq_extracted (H : BinaryGraph (n + 2) 3) (T : PhysicalPair n)
    (D : PairLabelFiber T) (a s : Fin 2)
    (hi : UniformBinaryContraction.UniqueInternalAt D.val.1 (H.permuteInternal D.val.2.symm) a s)
    (hd : UniformBinaryContraction.CoarseDistinct D.val.1 (H.permuteInternal D.val.2.symm))
    (hx : UniformBinaryContraction.ExitsDistinctAt D.val.1 (H.permuteInternal D.val.2.symm) a s) :
    physicalCoefficient H T = (-1 : ℝ) ^ s.val * rawWeight D.val.1
      (UniformBinaryContraction.curvatureGraph D.val.1 (H.permuteInternal D.val.2.symm) a s hi hd hx) :=
  (coefficient_eq_physical H T D).symm.trans (coefficient_eq_extracted D.val.1 _ a s hi hd hx)

theorem physicalCoefficient_zero_of_not_admissible (H : BinaryGraph (n + 2) 3)
    (T : PhysicalPair n) (D : PairLabelFiber T)
    (hD : ¬ UniformBinaryContraction.AdmissiblePair D.val.1 (H.permuteInternal D.val.2.symm)) :
    physicalCoefficient H T = 0 :=
  (coefficient_eq_physical H T D).symm.trans (coefficient_zero_of_not_admissible D.val.1 _ hD)

/-- Every physical pair occurs with the proved exact label multiplicity. -/
theorem sum_coefficients_eq_physical (H : BinaryGraph (n + 2) 3) :
    (∑ D : Fin (n + 1) × Equiv.Perm (Fin (n + 2)), coefficient D.1 (H.permuteInternal D.2.symm)) =
      (2 * (n + 1).factorial : ℕ) * ∑ T : PhysicalPair n, physicalCoefficient H T := by
  rw [← Fintype.sum_fiberwise (fun D : Fin (n + 1) × Equiv.Perm (Fin (n + 2)) ↦ movedPair D.1 D.2)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  calc
    _ = ∑ _D : PairLabelFiber T, physicalCoefficient H T :=
      Finset.sum_congr rfl (fun D _ ↦ coefficient_eq_physical H T D)
    _ = _ := by simp [nsmul_eq_mul,card_pairLabelFiber_all]

/-- The outgoing half-factor and quotient factorial cancel exactly against
the physical-pair internal fibre multiplicity. -/
theorem sum_averages_eq_physical (H : BinaryGraph (n + 2) 3) :
    (∑ D : Fin (n + 1) × Equiv.Perm (Fin (n + 2)),
      outgoingAverage (pairProfile D.1) (H.permuteInternal D.2.symm)) =
      ∑ T : PhysicalPair n, physicalCoefficient H T := by
  have hc : ((2 * (n + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hc
  rw [Finset.mul_sum]
  simpa only [coefficient_eq_average] using sum_coefficients_eq_physical H

/-- Final exact main curvature scalar table as actual physical-pair raw
quotient integrals. There are no local-to-global, covariance or coefficient
matching assumptions in this finite combinatorial identity. -/
theorem boundaryAverage_curvature_eq_physicalPairs (H : BinaryGraph (n + 2) 3) :
    boundaryAverage (curvatureProfile (canonicalWeight (k := ℝ))) H =
      (3 / 2 : ℝ) * ((n + 2).factorial : ℝ)⁻¹ *
        ∑ T : PhysicalPair n, physicalCoefficient H T := by
  have hc : curvatureProfile (canonicalWeight (k := ℝ) (n := n)) =
      (3 / 2 : ℝ) • ∑ i : Fin (n + 1), pairProfile i := by
    simpa only [pairProfile_eq] using (canonical_curvatureProfile_three_halves (k := ℝ) (n := n))
  rw [boundaryAverage, outgoingAverage_internalAverage, hc,
    outgoingAverage_smul, outgoingAverage_sum, internalAverage_apply]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  change ((n + 2).factorial : ℝ)⁻¹ *
    (∑ σ : Equiv.Perm (Fin (n + 2)), (3 / 2 : ℝ) *
      ∑ i : Fin (n + 1), outgoingAverage (pairProfile i) (H.permuteInternal σ.symm)) = _
  rw [← Finset.mul_sum]
  have hs : (∑ σ : Equiv.Perm (Fin (n + 2)), ∑ i : Fin (n + 1),
      outgoingAverage (pairProfile i) (H.permuteInternal σ.symm)) =
      ∑ T : PhysicalPair n, physicalCoefficient H T := by
    rw [Finset.sum_comm]
    simpa only [Fintype.sum_prod_type] using sum_averages_eq_physical H
  rw [hs]
  ring

end EnvelopingIsomorphism.Deformation.GraphCurvaturePhysicalPairs
