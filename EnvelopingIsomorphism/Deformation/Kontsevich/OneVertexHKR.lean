import EnvelopingIsomorphism.Deformation.HKRCocycle

/-!
# The labelled one-vertex sum and HKR normalization

This file proves the finite algebraic calculation for one interior vertex:
the outgoing-edge permutation sign appears once in the geometric weight and
once in the alternating tensor operator. An inverse-factorial-squared weight
per labelled graph therefore produces the factorial-normalized HKR cochain.
The corresponding values of the actual integrals are proved separately.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] {m : ℕ}

/-- The one-vertex operator for an outgoing-edge bijection, using the unnormalized
alternating tensor of the input wedge of derivations. -/
def oneVertexLabelledOperator (σ : Equiv.Perm (Fin m)) (a : A)
    (D : Fin m → Derivation K A A) : Cochain K A m :=
  (MultilinearMap.alternatization (derivationProduct a D)).toMultilinearMap.domDomCongr σ

theorem oneVertexLabelledOperator_apply (σ : Equiv.Perm (Fin m)) (a : A)
    (D : Fin m → Derivation K A A) (f : Fin m → A) :
    oneVertexLabelledOperator σ a D f = a * Matrix.det (fun i j => D j (f (σ i))) :=
  alternatingEvaluation_derivationProduct a D (fun i => f (σ i))

/-- A signed weight for each outgoing-edge bijection, with unsigned scalar `c`. -/
def oneVertexLabelledSum (c : K) (a : A) (D : Fin m → Derivation K A A) : Cochain K A m :=
  ∑ σ : Equiv.Perm (Fin m), c • (Equiv.Perm.sign σ • oneVertexLabelledOperator σ a D)

/-- The two permutation signs cancel, leaving exactly `m!` equal contributions. -/
theorem oneVertexLabelledSum_eq (c : K) (a : A) (D : Fin m → Derivation K A A) :
    oneVertexLabelledSum c a D = (c * (m.factorial : K)) •
      (MultilinearMap.alternatization (derivationProduct a D)).toMultilinearMap := by
  rw [oneVertexLabelledSum, ← Finset.smul_sum]
  change c •
    (MultilinearMap.alternatization
      (MultilinearMap.alternatization (derivationProduct a D)).toMultilinearMap).toMultilinearMap = _
  rw [AlternatingMap.coe_alternatization]
  simp only [Fintype.card_fin, AlternatingMap.coe_smul, ← Nat.cast_smul_eq_nsmul K, smul_smul]

/-- With the actual one-vertex weight `1/(m!)²`, the labelled sum is exactly HKR. -/
theorem oneVertexLabelledSum_factorial_eq_hkr [CharZero K] (a : A) (D : Fin m → Derivation K A A) :
    oneVertexLabelledSum ((m.factorial : K)⁻¹ ^ 2) a D = hkrCochain a D := by
  rw [oneVertexLabelledSum_eq]
  have hn : (m.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have heq : (m.factorial : K)⁻¹ ^ 2 * (m.factorial : K) = (m.factorial : K)⁻¹ := by
    rw [pow_two, mul_assoc, inv_mul_cancel₀ hn, mul_one]
  rw [heq]
  rfl

end EnvelopingIsomorphism.Deformation.Kontsevich
