import EnvelopingIsomorphism.Deformation.GraphWeightedInsertion
import EnvelopingIsomorphism.Deformation.GeneralGraphInternalPermutations
import EnvelopingIsomorphism.Deformation.GeneralGraphMixedProfiles

/-! Explicit averaging of scalar binary-vertex graph profiles.
Only operator covariance is used; no geometric weight is assumed invariant
under a relabelling of the normalized internal anchor. -/

noncomputable section
set_option maxSynthPendingDepth 3

namespace EnvelopingIsomorphism.Deformation.BinaryGraphAveraging

open scoped BigOperators Classical
open UniformBinaryGraphs GraphCoefficientProfiles

variable {k : Type*} [Field k] [CharZero k] {n d : ℕ}

/-- Average internal labels, retaining every original scalar weight. -/
def internalAverage (c : BinaryGraph n 3 → k) : BinaryGraph n 3 → k :=
  signedAverage (KontsevichGraph.General.Graph.permuteInternalEquiv 2 3) (fun _ ↦ 1) c

omit [CharZero k] in
theorem internalAverage_apply (c : BinaryGraph n 3 → k) (Γ : BinaryGraph n 3) :
    internalAverage c Γ = (n.factorial : k)⁻¹ *
      ∑ σ : Equiv.Perm (Fin n),
        c ((KontsevichGraph.General.Graph.permuteInternalEquiv 2 3 σ).symm Γ) := by
  simp [internalAverage, signedAverage, signedTransport, Fintype.card_perm]

omit [CharZero k] in
theorem ternaryValue_permuteInternal
    (π : GraphWeightedInsertion.Bivector (k := k) (d := d))
    (σ : Equiv.Perm (Fin n)) (Γ : BinaryGraph n 3) :
    GraphWeightedInsertion.ternaryValue π
        (KontsevichGraph.General.Graph.permuteInternalEquiv 2 3 σ Γ) =
      GraphWeightedInsertion.ternaryValue π Γ := by
  change cochainThreeEquiv k _
    ((Γ.permuteInternal σ).cochainOperator
      (fun _ ↦ Gauge.GraphTaylorCoefficients.coordinateTensor π)) = _
  rw [KontsevichGraph.General.Graph.cochainOperator_permuteInternal_identical]
  rfl

/-- Internal averaging changes no diagonal graph operator. -/
theorem evaluation_internalAverage
    (π : GraphWeightedInsertion.Bivector (k := k) (d := d)) (c : BinaryGraph n 3 → k) :
    evaluation (GraphWeightedInsertion.ternaryValue π) (internalAverage c) =
      evaluation (GraphWeightedInsertion.ternaryValue π) c := by
  apply evaluation_signedAverage
  · intro σ
    simp
  · intro σ Γ
    simpa using ternaryValue_permuteInternal π σ Γ

/-- Equality of the explicitly averaged scalar tables yields the actual
weighted operator equality, without any weight-invariance assumption. -/
theorem evaluation_eq_of_internalAverage_eq
    (π : GraphWeightedInsertion.Bivector (k := k) (d := d))
    {c e : BinaryGraph n 3 → k} (h : internalAverage c = internalAverage e) :
    evaluation (GraphWeightedInsertion.ternaryValue π) c =
      evaluation (GraphWeightedInsertion.ternaryValue π) e := by
  rw [← evaluation_internalAverage π c, ← evaluation_internalAverage π e, h]

omit [CharZero k] in
/-- The averaged fibre coefficient is the literal factorial-normalized finite
sum over internal vertex permutations and graph-producing assignments. -/
theorem internalAverage_pushforward_apply {ι : Type*} [Fintype ι]
    (f : ι → BinaryGraph n 3) (w : ι → k) (Γ : BinaryGraph n 3) :
    internalAverage (pushforward f w) Γ = (n.factorial : k)⁻¹ *
      ∑ σ : Equiv.Perm (Fin n), ∑ i,
        if (f i).permuteInternal σ = Γ then w i else 0 := by
  rw [internalAverage, signedAverage_pushforward_apply]
  simp only [Fintype.card_perm, Fintype.card_fin, one_mul]
  rfl

open KontsevichGraph.General

/-- The sign of an actual outgoing-slot relabelling, vertex by vertex. -/
def outgoingSign (τ : Fin n → Equiv.Perm (Fin 2)) : k :=
  ∏ v, permutationSign (R := k) (τ v)

omit [CharZero k] in
theorem outgoingSign_sq (τ : Fin n → Equiv.Perm (Fin 2)) :
    outgoingSign (k := k) τ * outgoingSign τ = 1 := by
  rw [outgoingSign, ← Finset.prod_mul_distrib]
  have hs (v : Fin n) : permutationSign (R := k) (τ v) * permutationSign (τ v) = 1 := by
    simp [permutationSign, ← Int.cast_mul, ← Units.val_mul]
  simp only [hs, Finset.prod_const_one]

omit [CharZero k] in
theorem coordinateTensor_permutationLaw
    (π : GraphWeightedInsertion.Bivector (k := k) (d := d)) :
    TensorPermutationLaw (Gauge.GraphTaylorCoefficients.coordinateTensor π) := by
  intro τ a
  have h := π.val.map_perm (fun i ↦ MvPolynomial.X (a i)) τ
  simpa only [Gauge.GraphTaylorCoefficients.coordinateTensor_apply,
    permutationSign, Function.comp_def, Units.smul_def, ← Int.cast_smul_eq_zsmul k] using h

omit [CharZero k] in
theorem ternaryValue_permuteOutgoing
    (π : GraphWeightedInsertion.Bivector (k := k) (d := d))
    (τ : Fin n → Equiv.Perm (Fin 2)) (Γ : BinaryGraph n 3) :
    GraphWeightedInsertion.ternaryValue π (Graph.outgoingGraphEquiv (fun _ ↦ 2) 3 τ Γ) =
      outgoingSign (k := k) τ • GraphWeightedInsertion.ternaryValue π Γ := by
  change cochainThreeEquiv k _
    ((Γ.permuteOutgoing τ).cochainOperator
      (fun _ ↦ Gauge.GraphTaylorCoefficients.coordinateTensor π)) = _
  rw [Graph.cochainOperator_permuteOutgoing_sign Γ τ _
    (fun _ ↦ coordinateTensor_permutationLaw π), map_smul]
  rfl

/-- A literal signed finite average over the two outgoing slots at every vertex. -/
def outgoingAverage (c : BinaryGraph n 3 → k) : BinaryGraph n 3 → k :=
  signedAverage (Graph.outgoingGraphEquiv (fun _ ↦ 2) 3) outgoingSign c

omit [CharZero k] in
theorem outgoingAverage_apply (c : BinaryGraph n 3 → k) (Γ : BinaryGraph n 3) :
    outgoingAverage c Γ = ((2 : k)^n)⁻¹ *
      ∑ τ : Fin n → Equiv.Perm (Fin 2), outgoingSign (k := k) τ *
        c (Γ.permuteOutgoing (fun v ↦ (τ v).symm)) := by
  simp [outgoingAverage, signedAverage, signedTransport,
    Fintype.card_perm]

theorem evaluation_outgoingAverage
    (π : GraphWeightedInsertion.Bivector (k := k) (d := d)) (c : BinaryGraph n 3 → k) :
    evaluation (GraphWeightedInsertion.ternaryValue π) (outgoingAverage c) =
      evaluation (GraphWeightedInsertion.ternaryValue π) c :=
  evaluation_signedAverage _ _ _ outgoingSign_sq (ternaryValue_permuteOutgoing π) c

/-- Both genuine graph relabellings are performed on scalar coefficient tables. -/
def boundaryAverage (c : BinaryGraph n 3 → k) : BinaryGraph n 3 → k :=
  outgoingAverage (internalAverage c)

omit [CharZero k] in
/-- The exact scalar table used by the boundary relation: no operator values occur. -/
theorem boundaryAverage_apply (c : BinaryGraph n 3 → k) (Γ : BinaryGraph n 3) :
    boundaryAverage c Γ = ((2 : k)^n)⁻¹ *
      ∑ τ : Fin n → Equiv.Perm (Fin 2), outgoingSign (k := k) τ *
        ((n.factorial : k)⁻¹ * ∑ σ : Equiv.Perm (Fin n),
          c ((Graph.permuteInternalEquiv 2 3 σ).symm
            (Γ.permuteOutgoing (fun v ↦ (τ v).symm)))) := by
  simp only [boundaryAverage, outgoingAverage_apply, internalAverage_apply]

theorem evaluation_boundaryAverage
    (π : GraphWeightedInsertion.Bivector (k := k) (d := d)) (c : BinaryGraph n 3 → k) :
    evaluation (GraphWeightedInsertion.ternaryValue π) (boundaryAverage c) =
      evaluation (GraphWeightedInsertion.ternaryValue π) c := by
  rw [boundaryAverage, evaluation_outgoingAverage, evaluation_internalAverage]

theorem evaluation_eq_of_boundaryAverage_eq
    (π : GraphWeightedInsertion.Bivector (k := k) (d := d))
    {c e : BinaryGraph n 3 → k} (h : boundaryAverage c = boundaryAverage e) :
    evaluation (GraphWeightedInsertion.ternaryValue π) c =
      evaluation (GraphWeightedInsertion.ternaryValue π) e := by
  rw [← evaluation_boundaryAverage π c, ← evaluation_boundaryAverage π e, h]

end EnvelopingIsomorphism.Deformation.BinaryGraphAveraging
