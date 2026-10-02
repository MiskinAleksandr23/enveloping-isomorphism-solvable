import EnvelopingIsomorphism.Deformation.GraphBoundaryProfiles
import EnvelopingIsomorphism.Deformation.MixedGraphBoundaryProfiles

/-! The finite scalar boundary equations commute with extension of their
coefficient field. In particular, real geometric identities suffice for the
complex identities used by the identification reduction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.GraphBoundaryScalarExtension

open scoped BigOperators Classical
open UniformBinaryGraphs GraphAssociatorProfiles GraphCurvatureProfiles
open MixedGraphProfileCarrier

variable {K k : Type*} [Field K] [CharZero K] [Field k] [CharZero k]

theorem map_associatorProfile (f : K →+* k) (N : ℕ)
    (w : (n : ℕ) → BinaryGraph n 2 → K) (H : BinaryGraph N 3) :
    f (associatorProfile N w H) =
      associatorProfile N (fun n Γ => f (w n Γ)) H := by
  simp [associatorProfile_apply, map_sum, apply_ite]

theorem map_curvatureProfile (f : K →+* k) {n : ℕ}
    (w : (i : Fin (n + 1)) → CurvatureGraph i → K) (H : BinaryGraph (n + 2) 3) :
    f (curvatureProfile w H) = curvatureProfile (fun i Γ => f (w i Γ)) H := by
  simp only [curvatureProfile_apply, map_mul, map_div₀, map_one, map_ofNat,
    map_sum, map_add, apply_ite, map_zero]

theorem map_boundaryAverage (f : K →+* k) {n : ℕ}
    (c : BinaryGraph n 3 → K) (H : BinaryGraph n 3) :
    f (BinaryGraphAveraging.boundaryAverage c H) =
      BinaryGraphAveraging.boundaryAverage (fun Γ => f (c Γ)) H := by
  simp [BinaryGraphAveraging.boundaryAverage_apply, BinaryGraphAveraging.outgoingSign,
    KontsevichGraph.General.permutationSign, map_sum, map_prod, map_ofNat]

theorem scalarBoundaryRelation_map (f : K →+* k)
    {w : (n : ℕ) → BinaryGraph n 2 → K}
    {v : (n : ℕ) → (i : Fin (n + 1)) → CurvatureGraph i → K}
    (h : GraphBoundaryProfiles.ScalarBoundaryRelation w v) :
    GraphBoundaryProfiles.ScalarBoundaryRelation
      (fun n Γ => f (w n Γ)) (fun n i Γ => f (v n i Γ)) := by
  intro n
  ext H
  simpa only [map_boundaryAverage, map_associatorProfile, map_curvatureProfile] using
    congrArg f (congrFun (h n) H)

theorem map_mixedBoundaryAverage (f : K →+* k) {n : ℕ}
    (c : VectorGraph n 2 → K) (H : VectorGraph n 2) :
    f (MixedGraphAveraging.boundaryAverage c H) =
      MixedGraphAveraging.boundaryAverage (fun Γ => f (c Γ)) H := by
  simp [MixedGraphAveraging.boundaryAverage_apply, MixedGraphAveraging.outgoingSign,
    KontsevichGraph.General.permutationSign, map_sum, map_prod, map_ofNat]

theorem map_sourceActionProfile (f : K →+* k) {n : ℕ}
    (w : BinaryGraph (n + 1) 2 → K) (H : VectorGraph (n + 1) 2) :
    f (MixedGraphActionSplits.sourceActionProfile w H) =
      MixedGraphActionSplits.sourceActionProfile (fun Γ => f (w Γ)) H := by
  simp only [MixedGraphActionSplits.sourceActionProfile, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, MixedGraphActionSplits.actionSplitProfile_apply,
    map_sum, map_mul, map_add, map_sub, apply_ite, map_one, map_zero]

theorem map_fullSourceActionProfile (f : K →+* k)
    (w : (n : ℕ) → BinaryGraph n 2 → K) (N : ℕ) (H : VectorGraph N 2) :
    f (MixedGraphSourceProfiles.fullSourceActionProfile w N H) =
      MixedGraphSourceProfiles.fullSourceActionProfile (fun n Γ => f (w n Γ)) N H := by
  cases N with
  | zero => simp [MixedGraphSourceProfiles.fullSourceActionProfile]
  | succ n => exact map_sourceActionProfile f _ _

theorem map_correctionProfile (f : K →+* k) {n : ℕ}
    (w : MixedGraphCorrectionProfiles.CorrectionGraph n → K) (H : VectorGraph (n + 2) 2) :
    f (MixedGraphCorrectionProfiles.correctionProfile w H) =
      MixedGraphCorrectionProfiles.correctionProfile (fun Γ => f (w Γ)) H := by
  simp only [MixedGraphCorrectionProfiles.correctionProfile_apply, map_mul, map_div₀,
    map_one, map_ofNat, map_sum, map_add, map_neg, apply_ite, map_zero]

theorem map_fullCorrectionProfile (f : K →+* k)
    (w : (n : ℕ) → MixedGraphCorrectionProfiles.CorrectionGraph n → K)
    (N : ℕ) (H : VectorGraph N 2) :
    f (MixedGraphBoundaryProfiles.fullCorrectionProfile w N H) =
      MixedGraphBoundaryProfiles.fullCorrectionProfile (fun n Γ => f (w n Γ)) N H := by
  rcases N with _ | (_ | n)
  · simp [MixedGraphBoundaryProfiles.fullCorrectionProfile]
  · simp [MixedGraphBoundaryProfiles.fullCorrectionProfile]
  · exact map_correctionProfile f _ _

theorem map_targetActionProfile (f : K →+* k) (N : ℕ)
    (w : (n : ℕ) → VectorGraph n 1 → K) (v : (n : ℕ) → BinaryGraph n 2 → K)
    (H : VectorGraph N 2) :
    f (MixedGraphTargetProfiles.targetActionProfile N w v H) =
      MixedGraphTargetProfiles.targetActionProfile N
        (fun n Γ => f (w n Γ)) (fun n Γ => f (v n Γ)) H := by
  simp [MixedGraphTargetProfiles.targetActionProfile, Finset.sum_apply,
    MixedGraphTargetProfiles.castProfile_apply, MixedGraphTargetProfiles.actionProfile,
    MixedGraphTargetProfiles.outputProfile_apply, MixedGraphTargetProfiles.inputProfile_apply,
    map_sum, apply_ite]

theorem scalarMixedBoundaryRelation_map (f : K →+* k)
    {w : (n : ℕ) → BinaryGraph n 2 → K}
    {v : (n : ℕ) → VectorGraph n 1 → K}
    {u : (n : ℕ) → MixedGraphCorrectionProfiles.CorrectionGraph n → K}
    (h : MixedGraphBoundaryProfiles.ScalarMixedBoundaryRelation w v u) :
    MixedGraphBoundaryProfiles.ScalarMixedBoundaryRelation
      (fun n Γ => f (w n Γ)) (fun n Γ => f (v n Γ)) (fun n Γ => f (u n Γ)) := by
  intro N
  ext H
  change MixedGraphAveraging.boundaryAverage
      (fun Γ => MixedGraphSourceProfiles.fullSourceActionProfile (fun n Γ => f (w n Γ)) N Γ +
        MixedGraphBoundaryProfiles.fullCorrectionProfile (fun n Γ => f (u n Γ)) N Γ) H =
    MixedGraphAveraging.boundaryAverage
      (fun Γ => MixedGraphTargetProfiles.targetActionProfile N
        (fun n Γ => f (v n Γ)) (fun n Γ => f (w n Γ)) Γ) H
  simpa only [map_mixedBoundaryAverage, Pi.add_apply, map_add,
    map_fullSourceActionProfile, map_fullCorrectionProfile, map_targetActionProfile] using
    congrArg f (congrFun (h N) H)

section RealWeights

variable [Algebra ℝ k]

omit [CharZero k] in
theorem map_canonicalBinaryWeight (n : ℕ) (Γ : BinaryGraph n 2) :
    algebraMap ℝ k (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ) n Γ) =
      GraphBoundaryProfiles.canonicalBinaryWeight (k := k) n Γ := by
  cases n with
  | zero => exact map_one _
  | succ n =>
    simp only [GraphBoundaryProfiles.canonicalBinaryWeight,
      Kontsevich.GeometricWeights.binaryWeightOver, Algebra.algebraMap_self_apply]

omit [CharZero k] in
theorem map_canonicalCurvatureWeight {n : ℕ} (i : Fin (n + 1)) (Γ : CurvatureGraph i) :
    algebraMap ℝ k (GraphCurvatureProfiles.canonicalWeight (k := ℝ) i Γ) =
      GraphCurvatureProfiles.canonicalWeight (k := k) i Γ := by
  simp only [GraphCurvatureProfiles.canonicalWeight, Algebra.algebraMap_self_apply]

omit [CharZero k] in
theorem map_canonicalVelocityWeight {n : ℕ} (Γ : VectorGraph n 1) :
    algebraMap ℝ k (MixedGraphBoundaryProfiles.canonicalVelocityWeight (k := ℝ) Γ) =
      MixedGraphBoundaryProfiles.canonicalVelocityWeight (k := k) Γ := by
  simp only [MixedGraphBoundaryProfiles.canonicalVelocityWeight, Algebra.algebraMap_self_apply]

omit [CharZero k] in
theorem map_canonicalQuotientWeight {n : ℕ}
    (Γ : MixedGraphCorrectionProfiles.CorrectionGraph n) :
    algebraMap ℝ k (MixedGraphCorrectionProfiles.canonicalQuotientWeight (k := ℝ) Γ) =
      MixedGraphCorrectionProfiles.canonicalQuotientWeight (k := k) Γ := by
  simp only [MixedGraphCorrectionProfiles.canonicalQuotientWeight, Algebra.algebraMap_self_apply]

/-- Extension of the real geometric equation preserves every scalar profile. -/
theorem canonicalScalarBoundaryRelation_of_real
    (h : GraphBoundaryProfiles.CanonicalScalarBoundaryRelation (k := ℝ)) :
    GraphBoundaryProfiles.CanonicalScalarBoundaryRelation (k := k) := by
  have hw : (fun n Γ => algebraMap ℝ k
      (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ) n Γ)) =
      GraphBoundaryProfiles.canonicalBinaryWeight (k := k) := by
    funext n Γ
    exact map_canonicalBinaryWeight n Γ
  have hv : (fun n i Γ => algebraMap ℝ k
      (GraphCurvatureProfiles.canonicalWeight (k := ℝ) (n := n) i Γ)) =
      (fun n => GraphCurvatureProfiles.canonicalWeight (k := k) (n := n)) := by
    funext n i Γ
    exact map_canonicalCurvatureWeight i Γ
  have hmap := scalarBoundaryRelation_map (algebraMap ℝ k) h
  rw [hw, hv] at hmap
  exact hmap

theorem canonicalScalarMixedBoundaryRelation_of_real
    (h : MixedGraphBoundaryProfiles.CanonicalScalarMixedBoundaryRelation (k := ℝ)) :
    MixedGraphBoundaryProfiles.CanonicalScalarMixedBoundaryRelation (k := k) := by
  have hw : (fun n Γ => algebraMap ℝ k
      (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ) n Γ)) =
      GraphBoundaryProfiles.canonicalBinaryWeight (k := k) := by
    funext n Γ
    exact map_canonicalBinaryWeight n Γ
  have hv : (fun n Γ => algebraMap ℝ k
      (MixedGraphBoundaryProfiles.canonicalVelocityWeight (k := ℝ) (n := n) Γ)) =
      (fun n => MixedGraphBoundaryProfiles.canonicalVelocityWeight (k := k) (n := n)) := by
    funext n Γ
    exact map_canonicalVelocityWeight Γ
  have hu : (fun n Γ => algebraMap ℝ k
      (MixedGraphCorrectionProfiles.canonicalQuotientWeight (k := ℝ) (n := n) Γ)) =
      (fun n => MixedGraphCorrectionProfiles.canonicalQuotientWeight (k := k) (n := n)) := by
    funext n Γ
    exact map_canonicalQuotientWeight Γ
  have hmap := scalarMixedBoundaryRelation_map (algebraMap ℝ k) h
  rw [hw, hv, hu] at hmap
  exact hmap

end RealWeights

theorem canonicalScalarBoundaryRelation_complex_of_real
    (h : GraphBoundaryProfiles.CanonicalScalarBoundaryRelation (k := ℝ)) :
    GraphBoundaryProfiles.CanonicalScalarBoundaryRelation (k := ℂ) :=
  canonicalScalarBoundaryRelation_of_real h

theorem canonicalScalarMixedBoundaryRelation_complex_of_real
    (h : MixedGraphBoundaryProfiles.CanonicalScalarMixedBoundaryRelation (k := ℝ)) :
    MixedGraphBoundaryProfiles.CanonicalScalarMixedBoundaryRelation (k := ℂ) :=
  canonicalScalarMixedBoundaryRelation_of_real h

end EnvelopingIsomorphism.Deformation.GraphBoundaryScalarExtension
