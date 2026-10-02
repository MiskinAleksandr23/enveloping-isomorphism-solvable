import EnvelopingIsomorphism.Deformation.MixedGraphRelabelling

/-! Genuine one-vector graph averaging on independently varying bivectors and a linear vector input. -/

noncomputable section
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedGraphAveraging
open scoped BigOperators Classical
open MixedGraphProfileCarrier KontsevichGraph.General GraphCoefficientProfiles
variable {n m d : ℕ}

abbrev OutgoingGroup (n : ℕ) := Fin n → Equiv.Perm (Fin 2)

/-- The selected one-slot fiber is fixed; every background two-slot fiber is transported explicitly. -/
def outgoingAt (i : Fin (n + 1)) (τ : OutgoingGroup n) (v : Fin (n + 1)) :
    Equiv.Perm (Fin (Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 i v)) :=
  if hv : v = i then Equiv.refl _ else
    (finCongr (show Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 i v = 2 from if_neg hv)).symm.permCongr
      (τ ((outsideEquiv i).symm ⟨v, hv⟩))

/-- Actual outgoing-slot graph permutations on every distinguished carrier placement. -/
def outgoingGraphEquiv (τ : OutgoingGroup n) (m : ℕ) : Equiv.Perm (VectorGraph n m) :=
  Equiv.sigmaCongrRight (fun i ↦ Graph.outgoingGraphEquiv _ m (outgoingAt i τ))

@[simp] theorem outgoingGraphEquiv_vertex (τ : OutgoingGroup n) (Γ : VectorGraph n m) :
    (outgoingGraphEquiv τ m Γ).vertex = Γ.vertex := rfl

variable {k : Type*} [Field k]

/-- The product of the n genuine binary slot signs, independent of the vector placement. -/
def outgoingSign (τ : OutgoingGroup n) : k := ∏ j, permutationSign (R := k) (τ j)

theorem outgoingSign_sq (τ : OutgoingGroup n) : outgoingSign (k := k) τ * outgoingSign τ = 1 :=
  BinaryGraphAveraging.outgoingSign_sq τ

@[simp] theorem outgoingAt_sign_root (i : Fin (n + 1)) (τ : OutgoingGroup n) :
    permutationSign (R := k) (outgoingAt i τ i) = 1 := by
  simp [outgoingAt, permutationSign]

@[simp] theorem outgoingAt_sign_background (i : Fin (n + 1)) (τ : OutgoingGroup n) (j : Fin n) :
    permutationSign (R := k) (outgoingAt i τ (placementEquiv i (Sum.inl j))) =
      permutationSign (R := k) (τ j) := by
  simp only [outgoingAt, dif_neg (placementEquiv_inl_ne i j), permutationSign,
    Equiv.Perm.sign_permCongr]
  have hj : (outsideEquiv i).symm
      ⟨placementEquiv i (Sum.inl j), placementEquiv_inl_ne i j⟩ = j := by
    change (outsideEquiv i).symm (outsideEquiv i j) = j
    exact (outsideEquiv i).symm_apply_apply j
  rw [hj]

@[simp] theorem outgoingAt_sign_vector (i : Fin (n + 1)) (τ : OutgoingGroup n) (j : Fin 1) :
    permutationSign (R := k) (outgoingAt i τ (placementEquiv i (Sum.inr j))) = 1 := by
  exact (congrArg (fun v ↦ permutationSign (R := k) (outgoingAt i τ v))
    (placementEquiv_inr i j)).trans (outgoingAt_sign_root i τ)

/-- The product over all actual vertex fibers is exactly the background slot sign. -/
theorem outgoingAt_sign_prod (i : Fin (n + 1)) (τ : OutgoingGroup n) :
    (∏ v, permutationSign (R := k) (outgoingAt i τ v)) = outgoingSign (k := k) τ := by
  rw [← (placementEquiv i).prod_comp (fun v ↦ permutationSign (R := k) (outgoingAt i τ v)),
    Fintype.prod_sum_type]
  simp only [outgoingAt_sign_background, outgoingAt_sign_vector,
    Finset.prod_const_one, mul_one]
  rfl

/-- Each actual multiderivation coordinate tensor obeys its native alternating slot law. -/
theorem rawTensor_permutationLaw {a : ℕ} (F : Multiderivation k (MvPolynomial (Fin d) k) a) :
    TensorPermutationLaw (SchoutenGraphContraction.rawTensor F) := by
  intro τ x
  have h := F.val.map_perm (fun i ↦ MvPolynomial.X (x i)) τ
  simpa only [SchoutenGraphContraction.rawTensor, permutationSign, Function.comp_def,
    Units.smul_def, ← Int.cast_smul_eq_zsmul k] using h

private theorem permutationLaw_of_heq {a b : ℕ} (ha : a = b)
    {T : Tensor a d k} {U : Tensor b d k} (hT : HEq T U) (hU : TensorPermutationLaw U) :
    TensorPermutationLaw T := by
  subst b
  rw [eq_of_heq hT]
  exact hU

theorem rawTensors_permutationLaw (i v : Fin (n + 1))
    (B : Fin (n + 1) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    TensorPermutationLaw (rawTensors i B X v) := by
  by_cases hv : v = i
  · subst v
    exact permutationLaw_of_heq (show Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 i i = 1 from if_pos rfl)
      (rawTensors_root_heq i B X) (rawTensor_permutationLaw X)
  · exact permutationLaw_of_heq (show Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 i v = 2 from if_neg hv)
      (rawTensors_other_heq i v hv B X) (rawTensor_permutationLaw (B v))

/-- Outgoing covariance includes all dependent coefficient tensors and the actual sign. -/
theorem rawValue_outgoingGraphEquiv (τ : OutgoingGroup n) (Γ : VectorGraph n m)
    (B : Fin (n + 1) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    rawValue (outgoingGraphEquiv τ m Γ) B X = outgoingSign (k := k) τ • rawValue Γ B X := by
  change (Γ.graph.permuteOutgoing (outgoingAt Γ.vertex τ)).cochainOperator (rawTensors Γ.vertex B X) = _
  rw [Graph.cochainOperator_permuteOutgoing_sign Γ.graph (outgoingAt Γ.vertex τ) _
    (fun v ↦ rawTensors_permutationLaw Γ.vertex v B X), outgoingAt_sign_prod]
  rfl

theorem operator_outgoingGraphEquiv (τ : OutgoingGroup n) (Γ : VectorGraph n m)
    (R : Fin n → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    operator (outgoingGraphEquiv τ m Γ) R X = outgoingSign (k := k) τ • operator Γ R X := by
  rw [operator_eq_filled, outgoingGraphEquiv_vertex, rawValue_outgoingGraphEquiv, ← operator_eq_filled]


abbrev MixedMap (k : Type*) [CommRing k] (d n : ℕ) :=
  MultilinearMap k (fun _ : Fin n ↦ Bivector (k := k) (d := d))
    (Vector (k := k) (d := d) →ₗ[k] Binary k (MvPolynomial (Fin d) k))

/-- Normalize the complete finite permutation sum on the n independent bivector inputs. -/
def symmetrize : MixedMap k d n →ₗ[k] MixedMap k d n :=
  (n.factorial : k)⁻¹ • ∑ σ : Equiv.Perm (Fin n),
    (MultilinearMap.domDomCongrLinearEquiv k k (Bivector (k := k) (d := d))
      (Vector (k := k) (d := d) →ₗ[k] Binary k (MvPolynomial (Fin d) k)) σ).toLinearMap

theorem symmetrize_apply (F : MixedMap k d n) (R : Fin n → Bivector (k := k) (d := d)) :
    symmetrize F R = (n.factorial : k)⁻¹ • ∑ σ : Equiv.Perm (Fin n), F (R ∘ σ) := by
  simp only [symmetrize, LinearMap.smul_apply, LinearMap.sum_apply, smul_apply, sum_apply]
  rfl

theorem symmetrize_domDomCongr (F : MixedMap k d n) (τ : Equiv.Perm (Fin n)) :
    symmetrize (F.domDomCongr τ) = symmetrize F := by
  apply MultilinearMap.ext
  intro R
  rw [symmetrize_apply, symmetrize_apply]
  congr 1
  apply Fintype.sum_equiv (Equiv.mulRight τ)
  intro σ
  rfl

/-- The genuine mixed multilinear graph map keeps its vector argument linear. -/
def symmetrizedBinaryValue (Γ : VectorGraph n 2) : MixedMap k d n := symmetrize (binaryValue Γ)

theorem symmetrizedBinaryValue_apply (Γ : VectorGraph n 2)
    (R : Fin n → Bivector (k := k) (d := d)) :
    symmetrizedBinaryValue Γ R = (n.factorial : k)⁻¹ •
      ∑ σ : Equiv.Perm (Fin n), binaryValue Γ (R ∘ σ) := symmetrize_apply _ _

theorem binaryValue_internalGraphEquiv (σ : Equiv.Perm (Fin (n + 1))) (Γ : VectorGraph n 2) :
    binaryValue (k := k) (d := d) (internalGraphEquiv σ 2 Γ) =
      (binaryValue Γ).domDomCongr (backgroundPerm Γ.vertex σ) := by
  apply MultilinearMap.ext
  intro R
  apply LinearMap.ext
  intro X
  change cochainTwoEquiv k _ (operator (internalGraphEquiv σ 2 Γ) R X) = _
  rw [operator_internalGraphEquiv]
  rfl

/-- The induced complement permutation disappears under input symmetrization. -/
theorem symmetrizedBinaryValue_internalGraphEquiv (σ : Equiv.Perm (Fin (n + 1)))
    (Γ : VectorGraph n 2) :
    symmetrizedBinaryValue (k := k) (d := d) (internalGraphEquiv σ 2 Γ) = symmetrizedBinaryValue Γ := by
  rw [symmetrizedBinaryValue, binaryValue_internalGraphEquiv, symmetrize_domDomCongr]
  rfl

theorem binaryValue_outgoingGraphEquiv (τ : OutgoingGroup n) (Γ : VectorGraph n 2) :
    binaryValue (k := k) (d := d) (outgoingGraphEquiv τ 2 Γ) =
      outgoingSign (k := k) τ • binaryValue (k := k) (d := d) Γ := by
  apply MultilinearMap.ext
  intro R
  apply LinearMap.ext
  intro X
  change cochainTwoEquiv k _ (operator (outgoingGraphEquiv τ 2 Γ) R X) =
    outgoingSign (k := k) τ • cochainTwoEquiv k _ (operator Γ R X)
  rw [operator_outgoingGraphEquiv, map_smul]

/-- The actual outgoing product sign remains after background symmetrization. -/
theorem symmetrizedBinaryValue_outgoingGraphEquiv (τ : OutgoingGroup n) (Γ : VectorGraph n 2) :
    symmetrizedBinaryValue (k := k) (d := d) (outgoingGraphEquiv τ 2 Γ) =
      outgoingSign (k := k) τ • symmetrizedBinaryValue (k := k) (d := d) Γ := by
  rw [symmetrizedBinaryValue, binaryValue_outgoingGraphEquiv, map_smul]
  rfl

variable [CharZero k]

theorem symmetrizedBinaryValue_diagonal (Γ : VectorGraph n 2)
    (π : Bivector (k := k) (d := d)) :
    symmetrizedBinaryValue Γ (fun _ ↦ π) = binaryValue Γ (fun _ ↦ π) := by
  rw [symmetrizedBinaryValue_apply]
  simp only [Function.comp_def, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul k, smul_smul]
  rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), one_smul]

/-- Average actual internal carrier relabellings, retaining every original scalar coefficient. -/
def internalAverage (c : VectorGraph n 2 → k) : VectorGraph n 2 → k :=
  signedAverage (fun σ : Equiv.Perm (Fin (n + 1)) ↦ internalGraphEquiv σ 2) (fun _ ↦ 1) c

/-- Signed scalar average over the actual n binary outgoing-slot permutations. -/
def outgoingAverage (c : VectorGraph n 2 → k) : VectorGraph n 2 → k :=
  signedAverage (fun τ : OutgoingGroup n ↦ outgoingGraphEquiv τ 2) outgoingSign c

/-- The complete scalar average used for the mixed boundary relation. -/
def boundaryAverage (c : VectorGraph n 2 → k) : VectorGraph n 2 → k :=
  outgoingAverage (internalAverage c)

omit [CharZero k] in
theorem internalAverage_apply (c : VectorGraph n 2 → k) (Γ : VectorGraph n 2) :
    internalAverage c Γ = ((n + 1).factorial : k)⁻¹ *
      ∑ σ : Equiv.Perm (Fin (n + 1)), c ((internalGraphEquiv σ 2).symm Γ) := by
  simp [internalAverage, signedAverage, signedTransport, Fintype.card_perm]

omit [CharZero k] in
theorem outgoingAverage_apply (c : VectorGraph n 2 → k) (Γ : VectorGraph n 2) :
    outgoingAverage c Γ = ((2 : k)^n)⁻¹ *
      ∑ τ : OutgoingGroup n, outgoingSign (k := k) τ * c ((outgoingGraphEquiv τ 2).symm Γ) := by
  simp [outgoingAverage, signedAverage, signedTransport, OutgoingGroup, Fintype.card_perm]

omit [CharZero k] in
/-- The full averaging table contains only actual inverse graph relabellings and scalar signs. -/
theorem boundaryAverage_apply (c : VectorGraph n 2 → k) (Γ : VectorGraph n 2) :
    boundaryAverage c Γ = ((2 : k)^n)⁻¹ *
      ∑ τ : OutgoingGroup n, outgoingSign (k := k) τ *
        (((n + 1).factorial : k)⁻¹ * ∑ σ : Equiv.Perm (Fin (n + 1)),
          c ((internalGraphEquiv σ 2).symm ((outgoingGraphEquiv τ 2).symm Γ))) := by
  simp only [boundaryAverage, outgoingAverage_apply, internalAverage_apply]

theorem evaluation_internalAverage (c : VectorGraph n 2 → k) :
    evaluation (symmetrizedBinaryValue (k := k) (d := d)) (internalAverage c) =
      evaluation (symmetrizedBinaryValue (k := k) (d := d)) c := by
  apply evaluation_signedAverage
  · intro σ
    simp
  · intro σ Γ
    simpa using symmetrizedBinaryValue_internalGraphEquiv (k := k) (d := d) σ Γ

theorem evaluation_outgoingAverage (c : VectorGraph n 2 → k) :
    evaluation (symmetrizedBinaryValue (k := k) (d := d)) (outgoingAverage c) =
      evaluation (symmetrizedBinaryValue (k := k) (d := d)) c :=
  evaluation_signedAverage _ _ _ outgoingSign_sq symmetrizedBinaryValue_outgoingGraphEquiv c

theorem evaluation_boundaryAverage (c : VectorGraph n 2 → k) :
    evaluation (symmetrizedBinaryValue (k := k) (d := d)) (boundaryAverage c) =
      evaluation (symmetrizedBinaryValue (k := k) (d := d)) c := by
  rw [boundaryAverage, evaluation_outgoingAverage, evaluation_internalAverage]

/-- A pure averaged scalar equality implies equality of the complete mixed multilinear maps. -/
theorem evaluation_eq_of_boundaryAverage_eq {c e : VectorGraph n 2 → k}
    (h : boundaryAverage c = boundaryAverage e) :
    evaluation (symmetrizedBinaryValue (k := k) (d := d)) c =
      evaluation (symmetrizedBinaryValue (k := k) (d := d)) e := by
  rw [← evaluation_boundaryAverage c, ← evaluation_boundaryAverage e, h]

theorem evaluation_diagonal (c : VectorGraph n 2 → k) (π : Bivector (k := k) (d := d)) :
    evaluation (symmetrizedBinaryValue (k := k) (d := d)) c (fun _ ↦ π) =
      evaluation (fun Γ ↦ binaryValue (k := k) (d := d) Γ (fun _ ↦ π)) c := by
  simp only [evaluation_apply, sum_apply, smul_apply, symmetrizedBinaryValue_diagonal]

end EnvelopingIsomorphism.Deformation.MixedGraphAveraging
