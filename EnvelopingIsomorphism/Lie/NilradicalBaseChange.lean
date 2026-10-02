import EnvelopingIsomorphism.Lie.Nilradical
import EnvelopingIsomorphism.Lie.NilpotentIdealAction
import EnvelopingIsomorphism.Lie.NilradicalTrace
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Flat.Equalizer

/-!
# Nilpotent Lie ideals under scalar extension

The lower central series for an ideal action commutes with scalar extension.
Consequently scalar extension preserves nilpotence of ordinary Lie ideals and
reflects it when the scalar extension is faithfully flat.
-/

namespace EnvelopingIsomorphism.Lie

open scoped TensorProduct

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  (A : Type*) [CommRing A] [Algebra R A]

/-- The ambient lower central series of an ideal action commutes with base change. -/
theorem ideal_lcs_baseChange (I : LieIdeal R L) (n : ℕ) :
    (I.lcs M n).baseChange A = LieIdeal.lcs (I.baseChange A) (A ⊗[R] M) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [LieIdeal.lcs_succ, LieIdeal.lcs_succ, LieSubmodule.lie_baseChange, ih]

/-- The lower central series of an ideal commutes with scalar extension. -/
theorem lowerCentralSeriesOfIdeal_baseChange (I : LieIdeal R L) (n : ℕ) :
    (lowerCentralSeriesOfIdeal I n).baseChange A =
      lowerCentralSeriesOfIdeal (I.baseChange A) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [lowerCentralSeriesOfIdeal_succ, lowerCentralSeriesOfIdeal_succ,
      LieSubmodule.lie_baseChange, ih]

/-- Scalar extension preserves nilpotence of the action of a Lie ideal. -/
theorem isNilpotent_baseChange_action (I : LieIdeal R L) [LieModule.IsNilpotent I M] :
    LieModule.IsNilpotent (I.baseChange A) (A ⊗[R] M) := by
  obtain ⟨n, hn⟩ := LieModule.IsNilpotent.nilpotent R I M
  have h : I.lcs M n = ⊥ := by
    simp only [← LieSubmodule.toSubmodule_inj, I.coe_lcs_eq, hn,
      LieSubmodule.bot_toSubmodule]
  apply (LieModule.isNilpotent_iff A (I.baseChange A) (A ⊗[R] M)).mpr
  refine ⟨n, ?_⟩
  rw [← LieSubmodule.toSubmodule_inj, ← LieIdeal.coe_lcs_eq (I.baseChange A),
    ← ideal_lcs_baseChange A I n, h, LieSubmodule.baseChange_bot,
    LieSubmodule.bot_toSubmodule]
  rfl

/-- Scalar extension preserves intrinsic nilpotence of a Lie ideal. -/
theorem isNilpotent_baseChange (I : LieIdeal R L) [LieRing.IsNilpotent I] :
    LieRing.IsNilpotent (I.baseChange A) := by
  haveI := isNilpotent_ideal_action I
  haveI := isNilpotent_baseChange_action (M := L) A I
  exact isNilpotent_of_ideal_action (I.baseChange A)

/-- Faithfully flat scalar extension reflects nilpotence of an ideal action. -/
theorem isNilpotent_of_baseChange_action [Module.FaithfullyFlat R A]
    (I : LieIdeal R L) [LieModule.IsNilpotent (I.baseChange A) (A ⊗[R] M)] :
    LieModule.IsNilpotent I M := by
  obtain ⟨n, hn⟩ :=
    LieModule.IsNilpotent.nilpotent A (I.baseChange A) (A ⊗[R] M)
  have hext : (I.lcs M n).baseChange A = ⊥ := by
    rw [ideal_lcs_baseChange, ← LieSubmodule.toSubmodule_inj,
      LieIdeal.coe_lcs_eq, hn, LieSubmodule.bot_toSubmodule]
    rfl
  have h : I.lcs M n = ⊥ := by
    rw [← LieSubmodule.toSubmodule_inj]
    apply Submodule.baseChange_injective (A := A)
    change ((I.lcs M n).baseChange A).toSubmodule =
      ((⊥ : LieSubmodule R L M).baseChange A).toSubmodule
    rw [hext, LieSubmodule.baseChange_bot]
  apply (LieModule.isNilpotent_iff R I M).mpr
  refine ⟨n, ?_⟩
  rw [← LieSubmodule.toSubmodule_inj, ← I.coe_lcs_eq, h,
    LieSubmodule.bot_toSubmodule]
  rfl

/-- Intrinsic nilpotence of an ideal can be checked after faithfully flat extension. -/
theorem isNilpotent_baseChange_iff [Module.FaithfullyFlat R A] (I : LieIdeal R L) :
    LieRing.IsNilpotent (I.baseChange A) ↔ LieRing.IsNilpotent I := by
  constructor
  · intro h
    haveI := h
    haveI := isNilpotent_ideal_action (I.baseChange A)
    haveI := isNilpotent_of_baseChange_action (M := L) A I
    exact isNilpotent_of_ideal_action I
  · intro h
    haveI := h
    exact isNilpotent_baseChange A I

/-- The scalar extension of the ordinary nilradical is contained in the new nilradical. -/
theorem nilradical_baseChange_le [IsNoetherian R L] :
    (nilradical R L).baseChange A ≤ nilradical A (A ⊗[R] L) := by
  haveI := isNilpotent_baseChange A (nilradical R L)
  exact le_nilradical ((nilradical R L).baseChange A)

section Trace

variable {k V : Type*} [Field k] [LieRing V] [LieAlgebra k V]
  (B : Type*) [CommRing B] [Algebra k B]

/-- The adjoint operator of a pure tensor is the corresponding scalar multiple. -/
theorem ad_tmul_baseChange (a : B) (x : V) :
    LieAlgebra.ad B (B ⊗[k] V) (a ⊗ₜ[k] x) = a • (LieAlgebra.ad k V x).baseChange B := by
  have h : a ⊗ₜ[k] x = a • (1 ⊗ₜ[k] x : B ⊗[k] V) :=
    TensorProduct.tmul_eq_smul_one_tmul a x
  rw [h, map_smul]
  congr 1
  exact LieModule.toEnd_baseChange k B V V x

/-- Base change sends an operator in the adjoint envelope into the new envelope. -/
theorem baseChange_mem_adjointEnvelope {T : Module.End k V}
    (hT : T ∈ adjointEnvelope k V) : T.baseChange B ∈ adjointEnvelope B (B ⊗[k] V) := by
  induction hT using Algebra.adjoin_induction with
  | mem T hT =>
    obtain ⟨x, rfl⟩ := hT
    change (LieModule.toEnd k V V x).baseChange B ∈ _
    rw [← LieModule.toEnd_baseChange k B V V x]
    exact ad_mem_adjointEnvelope (1 ⊗ₜ[k] x)
  | algebraMap r =>
    change (Module.End.baseChangeHom k B V) (algebraMap k (Module.End k V) r) ∈ _
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply k B (Module.End B (B ⊗[k] V))]
    exact (adjointEnvelope B (B ⊗[k] V)).algebraMap_mem _
  | add T S hT hS hTi hSi =>
    rw [LinearMap.baseChange_add]
    exact (adjointEnvelope B (B ⊗[k] V)).add_mem hTi hSi
  | mul T S hT hS hTi hSi =>
    rw [LinearMap.baseChange_mul]
    exact (adjointEnvelope B (B ⊗[k] V)).mul_mem hTi hSi

/-- The original finite trace tests, evaluated on the scalar extension. -/
noncomputable def extendedAdjointTraceTests {ι : Type*}
    (b : Module.Basis ι k (adjointEnvelope k V)) : B ⊗[k] V →ₗ[B] (ι → B) where
  toFun x i := LinearMap.trace B (B ⊗[k] V)
    (LieAlgebra.ad B (B ⊗[k] V) x * (b i : Module.End k V).baseChange B)
  map_add' x y := by ext i; simp [add_mul]
  map_smul' r x := by ext i; simp

variable [Module.Finite k V]

/-- On pure tensors the extended trace tests are the scalar extensions of the tests. -/
theorem extendedAdjointTraceTests_tmul {ι : Type*}
    (b : Module.Basis ι k (adjointEnvelope k V)) (a : B) (x : V) (i : ι) :
    extendedAdjointTraceTests B b (a ⊗ₜ[k] x) i =
      a * algebraMap k B (adjointTraceTests k V b x i) := by
  change LinearMap.trace B (B ⊗[k] V)
    (LieAlgebra.ad B (B ⊗[k] V) (a ⊗ₜ[k] x) * (b i : Module.End k V).baseChange B) = _
  rw [ad_tmul_baseChange, smul_mul_assoc, map_smul, ← LinearMap.baseChange_mul,
    LinearMap.trace_baseChange]
  rfl

/-- The finite trace-test map commutes with scalar extension. -/
theorem extendedAdjointTraceTests_eq_baseChange {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k (adjointEnvelope k V)) :
    extendedAdjointTraceTests B b =
      (TensorProduct.piScalarRight k B B ι).toLinearMap.comp
        ((adjointTraceTests k V b).baseChange B) := by
  ext a x
  simp [extendedAdjointTraceTests_tmul, Algebra.smul_def, mul_comm]

/-- Flatness identifies the kernel of the extended trace tests. -/
theorem ker_extendedAdjointTraceTests {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k (adjointEnvelope k V)) :
    LinearMap.ker (extendedAdjointTraceTests B b) =
      (adjointTraceIdeal k V).toSubmodule.baseChange B := by
  rw [extendedAdjointTraceTests_eq_baseChange, LinearEquiv.ker_comp]
  rw [← ker_adjointTraceTests b]
  exact Module.Flat.ker_lTensor_eq B B (adjointTraceTests k V b)

omit [Module.Finite k V] in
/-- The extended nilradical satisfies the original trace tests after scalar extension. -/
theorem nilradical_le_ker_extendedAdjointTraceTests [IsReduced B] {ι : Type*}
    (b : Module.Basis ι k (adjointEnvelope k V)) :
    (nilradical B (B ⊗[k] V)).toSubmodule ≤
      LinearMap.ker (extendedAdjointTraceTests B b) := by
  intro x hx
  apply LinearMap.mem_ker.mpr
  funext i
  exact nilradical_le_adjointTraceIdeal hx _
    (baseChange_mem_adjointEnvelope B (b i).property)

/-- The ordinary nilradical commutes with extension to any reduced coefficient algebra.

In particular this applies to every extension of characteristic-zero fields.
-/
theorem nilradical_baseChange [CharZero k] [IsReduced B] :
    (nilradical k V).baseChange B = nilradical B (B ⊗[k] V) := by
  apply le_antisymm (nilradical_baseChange_le B)
  let b := Module.finBasis k (adjointEnvelope k V)
  have h := nilradical_le_ker_extendedAdjointTraceTests B b
  rw [ker_extendedAdjointTraceTests, ← nilradical_eq_adjointTraceIdeal] at h
  exact h

/-- Every term of the nilradical's lower central series commutes with scalar extension. -/
theorem nilradical_lowerCentralSeries_baseChange [CharZero k] [IsReduced B] (n : ℕ) :
    (lowerCentralSeriesOfIdeal (nilradical k V) n).baseChange B =
      lowerCentralSeriesOfIdeal (nilradical B (B ⊗[k] V)) n := by
  rw [lowerCentralSeriesOfIdeal_baseChange, nilradical_baseChange]

end Trace

end EnvelopingIsomorphism.Lie
