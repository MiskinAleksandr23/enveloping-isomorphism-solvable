import EnvelopingIsomorphism.Identification.InitialApproximation
import EnvelopingIsomorphism.Rees.MarkedIsomorphism
import EnvelopingIsomorphism.Rees.EnvelopingScalarCoordinates
import EnvelopingIsomorphism.Descent.NilradicalFlag

/-!
# Recovered marked Rees data from an arbitrary enveloping-algebra equivalence

The record stores one common finite coordinate system and one weight function.
The Rees equivalence and its marked zero specialization are constructed from
the proved leading congruences, rather than supplied as assumptions.
-/

noncomputable section

namespace EnvelopingIsomorphism.Identification

open UniversalEnvelopingAlgebra
open EnvelopingIsomorphism Enveloping Lie PBW

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v w
variable (k : Type u) (L : Type v) (M : Type w) [Field k]
  [LieRing L] [LieAlgebra k L] [LieRing M] [LieAlgebra k M]

/-- Coherent finite data recovered from the actual associative equivalence. -/
structure RecoveredData where
  size : ℕ
  sourceBasis : Module.Basis (Fin size) k L
  targetBasis : Module.Basis (Fin size) k M
  weight : Fin size → ℕ
  source_adapted : IsLowerCentralAdapted sourceBasis weight (nilradical k L)
  target_adapted : IsLowerCentralAdapted targetBasis weight (nilradical k M)
  equiv : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M
  forward_leading : ∀ i, equiv (ι k (sourceBasis i)) - ι k (targetBasis i) ∈
    weightedLower targetBasis weight (weight i + 1)
  inverse_leading : ∀ i, equiv.symm (ι k (targetBasis i)) - ι k (sourceBasis i) ∈
    weightedLower sourceBasis weight (weight i + 1)

variable {k L M}

namespace RecoveredData

variable (D : RecoveredData k L M)

/-- The prescribed linear basis identification. It is not asserted to preserve the original brackets. -/
def linearEquiv : L ≃ₗ[k] M := D.sourceBasis.equiv D.targetBasis (Equiv.refl _)

@[simp] theorem linearEquiv_basis (i : Fin D.size) :
    D.linearEquiv (D.sourceBasis i) = D.targetBasis i :=
  Module.Basis.equiv_apply _ _ _ _

/-- The prescribed linear basis identification is an exact filtered equivalence. -/
theorem linearEquiv_map_filtration (d : ℕ) :
    (lowerCentralFiltration (nilradical k L) d).toSubmodule.map D.linearEquiv.toLinearMap =
      (lowerCentralFiltration (nilradical k M) d).toSubmodule := by
  rw [← D.source_adapted d, ← D.target_adapted d, Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, hi, (D.linearEquiv_basis i).symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨D.sourceBasis i, ⟨i, hi, rfl⟩, D.linearEquiv_basis i⟩

/-- Source Rees weights, with structural compatibility proved from nilradical adaptation. -/
def sourceWeightData : Rees.WeightData D.sourceBasis :=
  ⟨D.weight, adapted_bracket_weight D.sourceBasis D.weight (nilradical k L) D.source_adapted⟩

/-- Target Rees weights with the same weight function. -/
def targetWeightData : Rees.WeightData D.targetBasis :=
  ⟨D.weight, adapted_bracket_weight D.targetBasis D.weight (nilradical k M) D.target_adapted⟩

theorem weightData_eq : D.sourceWeightData.weight = D.targetWeightData.weight := rfl

/-- The actual polynomial Rees enveloping-algebra equivalence. -/
def reesEquiv : Rees.EnvelopingFamily.U D.sourceWeightData ≃ₐ[Polynomial k]
    Rees.EnvelopingFamily.U D.targetWeightData :=
  Rees.EnvelopingFamily.ofLeading D.sourceWeightData D.targetWeightData D.equiv rfl
    D.forward_leading D.inverse_leading

/-- The prescribed zero-fiber Lie identification, proved from the actual Rees equivalence. -/
def zeroLieEquiv : Rees.Family.Fiber D.sourceWeightData 0 ≃ₗ⁅k⁆
    Rees.Family.Fiber D.targetWeightData 0 :=
  Rees.EnvelopingFamily.zeroLieEquiv D.sourceWeightData D.targetWeightData D.equiv rfl
    D.forward_leading D.inverse_leading

/-- The true scalar specialization of the Rees algebra equivalence at zero. -/
def zeroSpecialization : UniversalEnvelopingAlgebra k (Rees.Family.Fiber D.sourceWeightData 0) ≃ₐ[k]
    UniversalEnvelopingAlgebra k (Rees.Family.Fiber D.targetWeightData 0) :=
  Rees.EnvelopingFamily.zeroSpecialization D.sourceWeightData D.targetWeightData D.equiv rfl
    D.forward_leading D.inverse_leading

@[simp] theorem zeroLieEquiv_basis (i : Fin D.size) :
    D.zeroLieEquiv (Rees.Family.fiberBasis D.sourceWeightData 0 i) =
      Rees.Family.fiberBasis D.targetWeightData 0 i :=
  Rees.EnvelopingFamily.zeroLieEquiv_basis _ _ _ _ _ _ i

@[simp] theorem zeroLieEquiv_toLinearEquiv :
    D.zeroLieEquiv.toLinearEquiv = (Rees.Family.fiberBasis D.sourceWeightData 0).equiv
      (Rees.Family.fiberBasis D.targetWeightData 0) (Equiv.refl (Fin D.size)) :=
  Rees.EnvelopingFamily.zeroLieEquiv_toLinearEquiv _ _ _ _ _ _

/-- The whole specialized enveloping map is the enveloping map of the prescribed marking. -/
theorem zeroSpecialization_eq_congr : D.zeroSpecialization = Enveloping.congr D.zeroLieEquiv :=
  Rees.EnvelopingFamily.zeroSpecialization_eq_congr _ _ _ _ _ _

/-- After the fixed marking, the whole zero specialization is the identity. -/
theorem identifiedZeroSpecialization_eq_refl :
    D.zeroSpecialization.trans (Enveloping.congr D.zeroLieEquiv).symm = AlgEquiv.refl :=
  Rees.EnvelopingFamily.identifiedZeroSpecialization_eq_refl _ _ _ _ _ _

/-- The stored leading congruences force the stored algebra equivalence to preserve augmentation. -/
theorem preserves_augmentation :
    (augmentation k M).comp D.equiv.toAlgHom = augmentation k L := by
  have hlinear : (augmentation k M).toLinearMap.comp
      (D.equiv.toLinearMap.comp (ι k).toLinearMap) = 0 := by
    apply D.sourceBasis.ext
    intro i
    change augmentation k M (D.equiv (ι k (D.sourceBasis i))) = 0
    have hi := D.forward_leading i
    rw [← adicPower_eq_weightedLower D.targetBasis D.weight (nilradical k M) D.target_adapted] at hi
    have hI : D.equiv (ι k (D.sourceBasis i)) - ι k (D.targetBasis i) ∈
        (envelopingIdeal (nilradical k M)).asIdeal :=
      Ideal.pow_le_self (Nat.succ_ne_zero _) hi
    have h := augmentation_eq_zero_of_mem_envelopingIdeal (nilradical k M)
      (TwoSidedIdeal.mem_asIdeal.mp hI)
    simpa only [map_sub, augmentation_ι, sub_zero] using h
  apply Enveloping.hom_ext_ι
  intro x
  change augmentation k M (D.equiv (ι k x)) = augmentation k L (ι k x)
  rw [augmentation_ι]
  exact LinearMap.congr_fun hlinear x

end RecoveredData

section ScalarExtension

open scoped TensorProduct
open Rees.EnvelopingScalarCoordinates

variable (K : Type*) [Field K] [Algebra k K]

/-- Scalar extension preserves every lower PBW support condition in the already chosen basis. -/
theorem weightedLower_baseChange_mem {α : Type*} [LinearOrder α]
    (b : Module.Basis α k L) (ω : α → ℕ) (d : ℕ)
    {a : UniversalEnvelopingAlgebra k L} (ha : a ∈ weightedLower b ω d) :
    (Enveloping.baseChangeEquiv k K L).symm (1 ⊗ₜ[k] a) ∈
      weightedLower (b.baseChange K) ω d := by
  apply (mem_weightedLower_iff _ _ _ _).mpr
  intro p hp
  have hc := Finsupp.mem_support_iff.mp hp
  rw [pbwCoeff_baseChange_symm_one_tmul] at hc
  apply (mem_weightedLower_iff b ω d a).mp ha p
  apply Finsupp.mem_support_iff.mpr
  intro hz
  exact hc (by rw [hz, map_zero])

/-- The exact native base-change equivalence preserves leading generator congruences. -/
theorem leadingGenerators_baseChange {α : Type*} [LinearOrder α]
    (b : Module.Basis α k L) (c : Module.Basis α k M) (ω : α → ℕ)
    (φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M)
    (hφ : ∀ i, φ (ι k (b i)) - ι k (c i) ∈ weightedLower c ω (ω i + 1)) :
    ∀ i, baseChangeAlgEquiv k K φ (ι K (b.baseChange K i)) - ι K (c.baseChange K i) ∈
      weightedLower (c.baseChange K) ω (ω i + 1) := by
  intro i
  convert weightedLower_baseChange_mem K c ω (ω i + 1) (hφ i) using 1
  simp only [Module.Basis.baseChange_apply, baseChangeAlgEquiv_ι_tmul,
    TensorProduct.tmul_sub, map_sub, Enveloping.baseChangeEquiv_symm_tmul_ι]

@[simp]
theorem baseChangeAlgEquiv_symm
    (φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M) :
    (baseChangeAlgEquiv k K φ).symm = baseChangeAlgEquiv k K φ.symm := by
  ext a
  rfl

namespace RecoveredData

variable [CharZero k]

/-- Extend the chosen bases, weights, and actual map. No bases or markings are reselected. -/
def baseChange (D : RecoveredData k L M) : RecoveredData K (K ⊗[k] L) (K ⊗[k] M) := by
  letI : Module.Finite k L := Module.Finite.of_basis D.sourceBasis
  letI : Module.Finite k M := Module.Finite.of_basis D.targetBasis
  exact
    { size := D.size
      sourceBasis := D.sourceBasis.baseChange K
      targetBasis := D.targetBasis.baseChange K
      weight := D.weight
      source_adapted := Descent.adapted_nilradical_basis_baseChange K _ _ D.source_adapted
      target_adapted := Descent.adapted_nilradical_basis_baseChange K _ _ D.target_adapted
      equiv := baseChangeAlgEquiv k K D.equiv
      forward_leading := leadingGenerators_baseChange K _ _ _ D.equiv D.forward_leading
      inverse_leading := by
        rw [baseChangeAlgEquiv_symm]
        exact leadingGenerators_baseChange K _ _ _ D.equiv.symm D.inverse_leading }

@[simp] theorem baseChange_size (D : RecoveredData k L M) : (D.baseChange K).size = D.size := rfl

@[simp] theorem baseChange_sourceBasis (D : RecoveredData k L M) :
    (D.baseChange K).sourceBasis = D.sourceBasis.baseChange K := rfl

@[simp] theorem baseChange_targetBasis (D : RecoveredData k L M) :
    (D.baseChange K).targetBasis = D.targetBasis.baseChange K := rfl

@[simp] theorem baseChange_weight (D : RecoveredData k L M) :
    (D.baseChange K).weight = D.weight := rfl

@[simp] theorem baseChange_equiv (D : RecoveredData k L M) :
    (D.baseChange K).equiv = baseChangeAlgEquiv k K D.equiv := rfl

/-- The chosen linear marking itself extends by scalars. -/
theorem baseChange_linearEquiv (D : RecoveredData k L M) :
    (D.baseChange K).linearEquiv = D.linearEquiv.baseChange k K L M := by
  have h : (D.baseChange K).linearEquiv.toLinearMap =
      (D.linearEquiv.baseChange k K L M).toLinearMap := by
    apply (D.sourceBasis.baseChange K).ext
    intro i
    change (D.baseChange K).linearEquiv ((D.baseChange K).sourceBasis i) =
      D.linearEquiv.baseChange k K L M (D.sourceBasis.baseChange K i)
    rw [(D.baseChange K).linearEquiv_basis]
    change D.targetBasis.baseChange K i =
      D.linearEquiv.baseChange k K L M (D.sourceBasis.baseChange K i)
    rw [Module.Basis.baseChange_apply, Module.Basis.baseChange_apply,
      LinearEquiv.baseChange_tmul, D.linearEquiv_basis]
  exact LinearEquiv.toLinearMap_injective h

end RecoveredData
end ScalarExtension

/-- The original hypotheses produce coherent recovered data with the explicit standard normalization. -/
theorem exists_recoveredData [CharZero k] [Module.Finite k L] [Module.Finite k M]
    [LieAlgebra.IsSolvable L]
    (φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M) :
    ∃ D : RecoveredData k L M, D.equiv = normalized φ := by
  obtain ⟨h₀, h₁, h₀', h₁'⟩ := initial_approximations_normalized φ
  obtain ⟨n, b, c, ω, e, hcb, hb, hc, hf, hg, hforward, hinverse⟩ :=
    exists_matched_adapted_leading_bases (normalized φ) (nilradical k L) (nilradical k M)
      h₀ h₁ h₀' h₁'
  exact ⟨⟨n, b, c, ω, hb, hc, normalized φ, hforward, hinverse⟩, rfl⟩

/-- A chosen recovered data set; all its fields have been constructed and proved above. -/
def recoveredData [CharZero k] [Module.Finite k L] [Module.Finite k M]
    [LieAlgebra.IsSolvable L]
    (φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M) :
    RecoveredData k L M :=
  Classical.choose (exists_recoveredData φ)

@[simp]
theorem recoveredData_equiv [CharZero k] [Module.Finite k L] [Module.Finite k M]
    [LieAlgebra.IsSolvable L]
    (φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M) :
    (recoveredData φ).equiv = normalized φ :=
  Classical.choose_spec (exists_recoveredData φ)

end EnvelopingIsomorphism.Identification
