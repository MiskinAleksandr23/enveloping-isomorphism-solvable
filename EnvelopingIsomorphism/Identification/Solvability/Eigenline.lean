import EnvelopingIsomorphism.Enveloping.UniversalProperties
import Mathlib.Algebra.Lie.LieTheorem
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! A surjection of enveloping algebras carries the common eigenline of the
pulled-back adjoint representation to a nonzero abelian ideal of the target. -/

namespace EnvelopingIsomorphism.Identification

universe u v w z
variable {k : Type u} [Field k]
variable {L : Type v} [LieRing L] [LieAlgebra k L]
variable {M : Type w} [LieRing M] [LieAlgebra k M]

attribute [local instance 100] LieRing.ofAssociativeRing

open UniversalEnvelopingAlgebra

/-- Stability under Lie generators implies stability under their enveloping algebra. -/
theorem stable_under_enveloping
    {V : Type z} [AddCommGroup V] [Module k V]
    (ρ : UniversalEnvelopingAlgebra k L →ₐ[k] Module.End k V)
    (P : Submodule k V)
    (hP : ∀ x : L, ∀ v ∈ P, ρ (ι k x) v ∈ P)
    (a : UniversalEnvelopingAlgebra k L) : ∀ v ∈ P, ρ a v ∈ P := by
  induction a using EnvelopingIsomorphism.Enveloping.induction with
  | scalar r =>
    intro v hv
    simpa using P.smul_mem r hv
  | generator x => exact hP x
  | mul a b ha hb =>
    intro v hv
    simpa only [map_mul, Module.End.mul_apply] using ha _ (hb _ hv)
  | add a b ha hb =>
    intro v hv
    simpa only [map_add, LinearMap.add_apply] using P.add_mem (ha _ hv) (hb _ hv)

/-- A nontrivial target has a nonzero abelian ideal whenever its enveloping algebra
is an algebra quotient of the enveloping algebra of a solvable Lie algebra. -/
theorem exists_nonzero_abelianIdeal_of_surjective_enveloping
    [CharZero k] [IsAlgClosed k] [LieAlgebra.IsSolvable L]
    [Module.Finite k M] [Nontrivial M]
    (Φ : UniversalEnvelopingAlgebra k L →ₐ[k] UniversalEnvelopingAlgebra k M)
    (hΦ : Function.Surjective Φ) :
    ∃ I : LieIdeal k M, I ≠ ⊥ ∧ ⁅I, I⁆ = ⊥ := by
  let ρ : UniversalEnvelopingAlgebra k L →ₐ[k] Module.End k M :=
    (lift k (LieAlgebra.ad k M)).comp Φ
  let π : L →ₗ⁅k⁆ Module.End k M := ρ.toLieHom.comp (ι k)
  letI : LieRingModule L M := LieRingModule.compLieHom M π
  letI : LieModule k L M := LieModule.compLieHom M π
  obtain ⟨χ, hχ⟩ := LieModule.exists_nontrivial_weightSpace_of_isSolvable k L M
  letI := hχ
  obtain ⟨v, hv⟩ := exists_ne (0 : LieModule.weightSpace M χ)
  have hv0 : (v : M) ≠ 0 := by simpa using hv
  have heigen (x : L) : ρ (ι k x) (v : M) = χ x • (v : M) := by
    exact ((LieModule.mem_weightSpace χ (v : M)).mp v.property) x
  let P : Submodule k M := k ∙ (v : M)
  have hgen : ∀ x : L, ∀ m ∈ P, ρ (ι k x) m ∈ P := by
    intro x m hm
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hm
    rw [map_smul, heigen]
    exact P.smul_mem _ (P.smul_mem _ (Submodule.mem_span_singleton_self _))
  have hstable : ∀ x : M, ∀ m ∈ P, ⁅x, m⁆ ∈ P := by
    intro x m hm
    obtain ⟨a, ha⟩ := hΦ (ι k x)
    have h := stable_under_enveloping ρ P hgen a m hm
    change lift k (LieAlgebra.ad k M) (Φ a) m ∈ P at h
    rw [ha, lift_ι_apply] at h
    exact h
  let I : LieIdeal k M := { P with lie_mem := fun {x m} hm => hstable x m hm }
  refine ⟨I, ?_, ?_⟩
  · intro hI
    have hmem : (v : M) ∈ I := Submodule.mem_span_singleton_self _
    rw [hI] at hmem
    exact hv0 hmem
  · apply le_antisymm _ bot_le
    rw [LieSubmodule.lie_le_iff]
    intro x hx y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
    simp

end EnvelopingIsomorphism.Identification
