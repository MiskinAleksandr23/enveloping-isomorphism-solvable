import EnvelopingIsomorphism.Deformation.GraphBoundaryProfiles

/-! Multilinear evaluation of scalar graph profiles on independently varying bivectors. -/

noncomputable section
set_option maxSynthPendingDepth 3
namespace EnvelopingIsomorphism.Deformation.SymmetrizedGraphProfiles

open scoped BigOperators Classical
open UniformBinaryGraphs GraphWeightedInsertion GraphCoefficientProfiles BinaryGraphAveraging

variable {k : Type*} [Field k] [CharZero k] {n d : ℕ}

abbrev ProfileMap (k : Type*) [CommRing k] (d n : ℕ) :=
  MultilinearMap k (fun _ : Fin n ↦ Bivector (k := k) (d := d))
    (Ternary k (MvPolynomial (Fin d) k))

/-- Averaging the actual input permutations is a linear operation on multilinear maps. -/
def symmetrize : ProfileMap k d n →ₗ[k] ProfileMap k d n :=
  (n.factorial : k)⁻¹ • ∑ σ : Equiv.Perm (Fin n),
    (MultilinearMap.domDomCongrLinearEquiv k k
      (Bivector (k := k) (d := d)) (Ternary k (MvPolynomial (Fin d) k)) σ).toLinearMap

omit [CharZero k] in
theorem symmetrize_apply (F : ProfileMap k d n) (R : Fin n → Bivector (k := k) (d := d)) :
    symmetrize F R = (n.factorial : k)⁻¹ • ∑ σ : Equiv.Perm (Fin n), F (R ∘ σ) := by
  simp only [symmetrize, LinearMap.smul_apply, LinearMap.sum_apply,
    smul_apply, sum_apply]
  rfl

omit [CharZero k] in
theorem symmetrize_domDomCongr (F : ProfileMap k d n) (τ : Equiv.Perm (Fin n)) :
    symmetrize (F.domDomCongr τ) = symmetrize F := by
  apply MultilinearMap.ext
  intro R
  rw [symmetrize_apply, symmetrize_apply]
  congr 1
  apply Fintype.sum_equiv (Equiv.mulRight τ)
  intro σ
  rfl

theorem symmetrize_diagonal (F : ProfileMap k d n) (π : Bivector (k := k) (d := d)) :
    symmetrize F (fun _ ↦ π) = F (fun _ ↦ π) := by
  rw [symmetrize_apply]
  simp only [Function.comp_def, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul k, smul_smul]
  rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), one_smul]

/-- The genuine ordered graph operator as a multilinear map into ternary cochains. -/
def ternaryMap (Γ : BinaryGraph n 3) : ProfileMap k d n :=
  (cochainThreeEquiv k (MvPolynomial (Fin d) k)).toLinearMap.compMultilinearMap (operator Γ)

omit [CharZero k] in
@[simp] theorem ternaryMap_apply (Γ : BinaryGraph n 3)
    (R : Fin n → Bivector (k := k) (d := d)) :
    ternaryMap Γ R = cochainThreeEquiv k _ (operator Γ R) := rfl

/-- The normalized symmetrized graph operator retains independent bivector inputs. -/
def symmetrizedValue (Γ : BinaryGraph n 3) : ProfileMap k d n := symmetrize (ternaryMap Γ)

omit [CharZero k] in
theorem symmetrizedValue_apply (Γ : BinaryGraph n 3)
    (R : Fin n → Bivector (k := k) (d := d)) :
    symmetrizedValue Γ R = (n.factorial : k)⁻¹ •
      ∑ σ : Equiv.Perm (Fin n), cochainThreeEquiv k _ (operator Γ (R ∘ σ)) :=
  symmetrize_apply _ _

theorem symmetrizedValue_diagonal (Γ : BinaryGraph n 3)
    (π : Bivector (k := k) (d := d)) :
    symmetrizedValue Γ (fun _ ↦ π) = ternaryValue π Γ := symmetrize_diagonal _ _

omit [CharZero k] in
theorem ternaryMap_permuteInternal (Γ : BinaryGraph n 3) (σ : Equiv.Perm (Fin n)) :
    ternaryMap (k := k) (d := d) (Γ.permuteInternal σ) = (ternaryMap Γ).domDomCongr σ := by
  apply MultilinearMap.ext
  intro R
  change cochainThreeEquiv k _ ((Γ.permuteInternal σ).cochainOperator
    (fun v ↦ Gauge.GraphTaylorCoefficients.coordinateTensor (R v))) = _
  rw [KontsevichGraph.General.Graph.cochainOperator_permuteInternal_covariance]
  rfl

omit [CharZero k] in
theorem symmetrizedValue_permuteInternal (σ : Equiv.Perm (Fin n)) (Γ : BinaryGraph n 3) :
    symmetrizedValue (k := k) (d := d)
      (KontsevichGraph.General.Graph.permuteInternalEquiv 2 3 σ Γ) = symmetrizedValue Γ := by
  change symmetrize (ternaryMap (Γ.permuteInternal σ)) = _
  rw [ternaryMap_permuteInternal, symmetrize_domDomCongr]
  rfl

omit [CharZero k] in
theorem ternaryMap_permuteOutgoing (Γ : BinaryGraph n 3)
    (τ : Fin n → Equiv.Perm (Fin 2)) :
    ternaryMap (k := k) (d := d) (Γ.permuteOutgoing τ) = outgoingSign (k := k) τ • ternaryMap (k := k) (d := d) Γ := by
  apply MultilinearMap.ext
  intro R
  change cochainThreeEquiv k _ ((Γ.permuteOutgoing τ).cochainOperator
    (fun v ↦ Gauge.GraphTaylorCoefficients.coordinateTensor (R v))) = _
  rw [KontsevichGraph.General.Graph.cochainOperator_permuteOutgoing_sign Γ τ _
    (fun v ↦ coordinateTensor_permutationLaw (R v)), map_smul]
  rfl

omit [CharZero k] in
theorem symmetrizedValue_permuteOutgoing (τ : Fin n → Equiv.Perm (Fin 2))
    (Γ : BinaryGraph n 3) :
    symmetrizedValue (k := k) (d := d)
      (KontsevichGraph.General.Graph.outgoingGraphEquiv (fun _ ↦ 2) 3 τ Γ) =
        outgoingSign (k := k) τ • symmetrizedValue (k := k) (d := d) Γ := by
  change symmetrize (ternaryMap (Γ.permuteOutgoing τ)) = _
  rw [ternaryMap_permuteOutgoing, map_smul]
  rfl

theorem evaluation_internalAverage (c : BinaryGraph n 3 → k) :
    evaluation (symmetrizedValue (k := k) (d := d)) (internalAverage c) =
      evaluation (symmetrizedValue (k := k) (d := d)) c := by
  apply evaluation_signedAverage
  · intro σ
    simp
  · intro σ Γ
    simpa using symmetrizedValue_permuteInternal (k := k) (d := d) σ Γ

theorem evaluation_outgoingAverage (c : BinaryGraph n 3 → k) :
    evaluation (symmetrizedValue (k := k) (d := d)) (outgoingAverage c) =
      evaluation (symmetrizedValue (k := k) (d := d)) c :=
  evaluation_signedAverage _ _ _ outgoingSign_sq symmetrizedValue_permuteOutgoing c

theorem evaluation_boundaryAverage (c : BinaryGraph n 3 → k) :
    evaluation (symmetrizedValue (k := k) (d := d)) (boundaryAverage c) =
      evaluation (symmetrizedValue (k := k) (d := d)) c := by
  rw [boundaryAverage, evaluation_outgoingAverage, evaluation_internalAverage]

/-- Equality of pure scalar averages yields equality of the full multilinear maps. -/
theorem evaluation_eq_of_boundaryAverage_eq {c e : BinaryGraph n 3 → k}
    (h : boundaryAverage c = boundaryAverage e) :
    evaluation (symmetrizedValue (k := k) (d := d)) c = evaluation (symmetrizedValue (k := k) (d := d)) e := by
  rw [← evaluation_boundaryAverage c, ← evaluation_boundaryAverage e, h]

theorem evaluation_diagonal (c : BinaryGraph n 3 → k)
    (π : Bivector (k := k) (d := d)) :
    evaluation (symmetrizedValue (k := k) (d := d)) c (fun _ ↦ π) = evaluation (ternaryValue π) c := by
  simp only [evaluation_apply, sum_apply, smul_apply,
    symmetrizedValue_diagonal]

/-- The scalar boundary relation acts on independent inputs without a polarization premise. -/
theorem boundaryRelation_multilinear
    {w : (n : ℕ) → BinaryGraph n 2 → k}
    {v : (n : ℕ) → (i : Fin (n + 1)) → GraphCurvatureProfiles.CurvatureGraph i → k}
    (h : GraphBoundaryProfiles.ScalarBoundaryRelation w v) (n : ℕ) :
    evaluation (symmetrizedValue (k := k) (d := d)) (GraphAssociatorProfiles.associatorProfile (n + 2) w) =
      evaluation (symmetrizedValue (k := k) (d := d)) (GraphCurvatureProfiles.curvatureProfile (v n)) :=
  evaluation_eq_of_boundaryAverage_eq (h n)

end EnvelopingIsomorphism.Deformation.SymmetrizedGraphProfiles
