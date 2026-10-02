import EnvelopingIsomorphism.Identification.MetabelianNilradicalData
import EnvelopingIsomorphism.Identification.PolynomialPartBaseChange
import EnvelopingIsomorphism.Identification.PolynomialPartEquiv
import EnvelopingIsomorphism.Enveloping.LieQuotientBaseChange
import EnvelopingIsomorphism.Lie.NilradicalBaseChange
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! The actual nilradical-derived quotient and its abelian ideal commute
with field extension; HQ2 then descends from an algebraic closure. -/

noncomputable section
namespace EnvelopingIsomorphism.Identification

open scoped TensorProduct
open EnvelopingIsomorphism.Lie

variable {k L : Type*} [Field k] [LieRing L] [LieAlgebra k L]
variable (K : Type*) [Field K] [Algebra k K]

def quotientLieEquivOfEq {A : Type*} [LieRing A] [LieAlgebra k A]
    {I J : LieIdeal k A} (h : I = J) : (A ⧸ I) ≃ₗ⁅k⁆ A ⧸ J := by
  subst J
  exact LieEquiv.refl

@[simp] theorem quotientLieEquivOfEq_mk {A : Type*} [LieRing A] [LieAlgebra k A]
    {I J : LieIdeal k A} (h : I = J) (x : A) :
    quotientLieEquivOfEq h (quotientLieHom I x) = quotientLieHom J x := by
  subst J
  rfl

/-- Scalar extension of the original derived-ideal quotient, as a genuine Lie equivalence. -/
def idealDerivedQuotientBaseChangeEquiv (N : LieIdeal k L) :
    K ⊗[k] idealDerivedQuotient N ≃ₗ⁅K⁆ idealDerivedQuotient (N.baseChange K) :=
  (Enveloping.lieQuotientBaseChangeEquiv K ⁅N, N⁆).trans
    (quotientLieEquivOfEq
      (LieSubmodule.lie_baseChange (R := k) (A := K) (L := L) (M := L)))

@[simp] theorem idealDerivedQuotientBaseChangeEquiv_tmul (N : LieIdeal k L) (a : K) (x : L) :
    idealDerivedQuotientBaseChangeEquiv K N (a ⊗ₜ[k] quotientLieHom ⁅N, N⁆ x) =
      quotientLieHom ⁅N.baseChange K, N.baseChange K⁆ (a ⊗ₜ[k] x) := by
  change quotientLieEquivOfEq _
    (Enveloping.lieQuotientBaseChangeEquiv K ⁅N, N⁆
      (a ⊗ₜ[k] quotientLieHom ⁅N, N⁆ x)) = _
  rw [show quotientLieHom ⁅N, N⁆ x = Enveloping.lieQuotientMap ⁅N, N⁆ x from rfl,
    Enveloping.lieQuotientBaseChangeEquiv_tmul]
  exact quotientLieEquivOfEq_mk _ _

/-- The equivalence identifies the actual scalar-extended abelian ideal image. -/
theorem idealAbelianImage_map_baseChangeEquiv (N : LieIdeal k L) :
    LieIdeal.map (idealDerivedQuotientBaseChangeEquiv K N).toLieHom
      ((idealAbelianImage N).baseChange K) =
      idealAbelianImage (N.baseChange K) := by
  let e := idealDerivedQuotientBaseChangeEquiv K N
  apply le_antisymm
  · intro x hx
    obtain ⟨⟨z, hzmem⟩, hz⟩ := LieIdeal.mem_map_of_surjective e.surjective hx
    rw [← hz]
    change e z ∈ idealAbelianImage (N.baseChange K)
    clear hx hz x
    rw [LieSubmodule.mem_baseChange_iff] at hzmem
    induction hzmem using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, hy, rfl⟩ := hz
      obtain ⟨n, hn⟩ := LieIdeal.mem_map_of_surjective (quotientLieHom_surjective ⁅N, N⁆) hy
      change e ((1 : K) ⊗ₜ[k] y) ∈ _
      rw [← hn, idealDerivedQuotientBaseChangeEquiv_tmul]
      exact LieIdeal.mem_map (LieSubmodule.tmul_mem_baseChange_of_mem 1 n.property)
    | zero => simp
    | add y z _ _ hy hz => simpa only [map_add] using add_mem hy hz
    | smul a y _ hy =>
      rw [map_smul]
      exact (idealAbelianImage (N.baseChange K)).smul_mem a hy
  · intro x hx
    obtain ⟨⟨z, hzmem⟩, hz⟩ := LieIdeal.mem_map_of_surjective
      (quotientLieHom_surjective ⁅N.baseChange K, N.baseChange K⁆) hx
    rw [← hz]
    change quotientLieHom ⁅N.baseChange K, N.baseChange K⁆ z ∈
      LieIdeal.map e.toLieHom ((idealAbelianImage N).baseChange K)
    clear hx hz x
    rw [LieSubmodule.mem_baseChange_iff] at hzmem
    induction hzmem using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨n, hn, rfl⟩ := hz
      change quotientLieHom ⁅N.baseChange K, N.baseChange K⁆ ((1 : K) ⊗ₜ[k] n) ∈ _
      rw [← idealDerivedQuotientBaseChangeEquiv_tmul]
      exact LieIdeal.mem_map
        (LieSubmodule.tmul_mem_baseChange_of_mem 1 (LieIdeal.mem_map hn))
    | zero => simp
    | add y z _ _ hy hz => simpa only [map_add] using add_mem hy hz
    | smul a y _ hy =>
      rw [map_smul]
      exact (LieIdeal.map e.toLieHom ((idealAbelianImage N).baseChange K)).smul_mem a hy

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Descent of the hard LN inclusion across an arbitrary field extension. -/
theorem LN_subset_polynomialPart_of_baseChange (N : LieIdeal k L)
    (hK : LN K (UniversalEnvelopingAlgebra K (idealDerivedQuotient (N.baseChange K))) ⊆
      (idealPolynomialPart (idealAbelianImage (N.baseChange K)) : Set _)) :
    LN k (UniversalEnvelopingAlgebra k (idealDerivedQuotient N)) ⊆
      (idealPolynomialPart (idealAbelianImage N) : Set _) := by
  intro a ha
  let e := idealDerivedQuotientBaseChangeEquiv K N
  let u := (Enveloping.baseChangeEquiv k K (idealDerivedQuotient N)).symm ((1 : K) ⊗ₜ[k] a)
  have hu : u ∈ LN K (UniversalEnvelopingAlgebra K (K ⊗[k] idealDerivedQuotient N)) :=
    (mem_LN_map_iff (Enveloping.baseChangeEquiv k K (idealDerivedQuotient N)).symm _).mpr
      ((mem_LN_one_tmul_iff (K := K) a).mpr ha)
  have he := hK ((mem_LN_map_iff (Enveloping.congr e) u).mpr hu)
  rw [← idealAbelianImage_map_baseChangeEquiv K N] at he
  have huP := (mem_idealPolynomialPart_equiv_iff e ((idealAbelianImage N).baseChange K) u).mp he
  exact (mem_idealPolynomialPart_baseChange_iff (K := K) (idealAbelianImage N) a).mp huP

/-- Descent of the hard LF inclusion across an arbitrary field extension. -/
theorem LF_subset_linearPolynomialPart_of_baseChange (N : LieIdeal k L)
    (hK : LF K (UniversalEnvelopingAlgebra K (idealDerivedQuotient (N.baseChange K))) ⊆
      (linearPolynomialPart (idealAbelianImage (N.baseChange K)) : Set _)) :
    LF k (UniversalEnvelopingAlgebra k (idealDerivedQuotient N)) ⊆
      (linearPolynomialPart (idealAbelianImage N) : Set _) := by
  intro a ha
  let e := idealDerivedQuotientBaseChangeEquiv K N
  let u := (Enveloping.baseChangeEquiv k K (idealDerivedQuotient N)).symm ((1 : K) ⊗ₜ[k] a)
  have hu : u ∈ LF K (UniversalEnvelopingAlgebra K (K ⊗[k] idealDerivedQuotient N)) :=
    (mem_LF_map_iff (Enveloping.baseChangeEquiv k K (idealDerivedQuotient N)).symm _).mpr
      ((mem_LF_one_tmul_iff (K := K) a).mpr ha)
  have he := hK ((mem_LF_map_iff (Enveloping.congr e) u).mpr hu)
  rw [← idealAbelianImage_map_baseChangeEquiv K N] at he
  have huP := (mem_linearPolynomialPart_equiv_iff e ((idealAbelianImage N).baseChange K) u).mp he
  exact (mem_linearPolynomialPart_baseChange_iff (K := K) (idealAbelianImage N) a).mp huP

section Nilradical

variable [CharZero k] [Module.Finite k L] [LieAlgebra.IsSolvable L]

/-- Canonical hard LN inclusion over an arbitrary characteristic-zero field.
No eigenweight or algebraic-closedness hypothesis remains. -/
theorem LN_subset_polynomialPart_nilradical_derivedQuotient :
    LN k (UniversalEnvelopingAlgebra k (idealDerivedQuotient (nilradical k L))) ⊆
      (idealPolynomialPart (idealAbelianImage (nilradical k L)) : Set _) := by
  let Ω := AlgebraicClosure k
  apply LN_subset_polynomialPart_of_baseChange Ω (nilradical k L)
  rw [nilradical_baseChange]
  intro a ha
  exact (hq2_nilradical_derivedQuotient (M := Ω ⊗[k] L) a).1.mp ha

/-- Canonical hard LF inclusion over an arbitrary characteristic-zero field.
This is the second input needed by the initial leading approximations. -/
theorem LF_subset_linearPolynomialPart_nilradical_derivedQuotient :
    LF k (UniversalEnvelopingAlgebra k (idealDerivedQuotient (nilradical k L))) ⊆
      (linearPolynomialPart (idealAbelianImage (nilradical k L)) : Set _) := by
  let Ω := AlgebraicClosure k
  apply LF_subset_linearPolynomialPart_of_baseChange Ω (nilradical k L)
  rw [nilradical_baseChange]
  intro a ha
  apply (mem_linearPolynomialPart_iff _ a).mpr
  exact (hq2_nilradical_derivedQuotient (M := Ω ⊗[k] L) a).2.mp ha

theorem LN_eq_polynomialPart_nilradical_derivedQuotient_anyField :
    LN k (UniversalEnvelopingAlgebra k (idealDerivedQuotient (nilradical k L))) =
      (idealPolynomialPart (idealAbelianImage (nilradical k L)) : Set _) :=
  Set.Subset.antisymm LN_subset_polynomialPart_nilradical_derivedQuotient
    (idealPolynomialPart_subset_LN (idealAbelianImage (nilradical k L)))

theorem LF_eq_linearPolynomialPart_nilradical_derivedQuotient_anyField :
    LF k (UniversalEnvelopingAlgebra k (idealDerivedQuotient (nilradical k L))) =
      (linearPolynomialPart (idealAbelianImage (nilradical k L)) : Set _) := by
  apply Set.Subset.antisymm LF_subset_linearPolynomialPart_nilradical_derivedQuotient
  intro a ha
  obtain ⟨x, p, hp, rfl⟩ := (mem_linearPolynomialPart_iff _ a).mp ha
  exact linear_add_idealPolynomialPart_mem_LF _ x hp

/-- Both exact canonical HQ2 descriptions over the original field. -/
theorem hq2_nilradical_derivedQuotient_anyField
    (a : UniversalEnvelopingAlgebra k (idealDerivedQuotient (nilradical k L))) :
    (a ∈ LN k (UniversalEnvelopingAlgebra k (idealDerivedQuotient (nilradical k L))) ↔
      a ∈ idealPolynomialPart (idealAbelianImage (nilradical k L))) ∧
    (a ∈ LF k (UniversalEnvelopingAlgebra k (idealDerivedQuotient (nilradical k L))) ↔
      a ∈ linearPolynomialPart (idealAbelianImage (nilradical k L))) := by
  rw [LN_eq_polynomialPart_nilradical_derivedQuotient_anyField,
    LF_eq_linearPolynomialPart_nilradical_derivedQuotient_anyField]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- The C1 commutativity conclusion over any characteristic-zero field. -/
theorem lie_eq_zero_of_LN_nilradical_derivedQuotient_anyField
    (a b : UniversalEnvelopingAlgebra k (idealDerivedQuotient (nilradical k L)))
    (ha : a ∈ LN k (UniversalEnvelopingAlgebra k (idealDerivedQuotient (nilradical k L))))
    (hb : b ∈ LN k (UniversalEnvelopingAlgebra k (idealDerivedQuotient (nilradical k L)))) :
    ⁅a, b⁆ = 0 :=
  lie_eq_zero_of_mem_idealPolynomialPart (idealAbelianImage (nilradical k L))
    (LN_subset_polynomialPart_nilradical_derivedQuotient ha)
    (LN_subset_polynomialPart_nilradical_derivedQuotient hb)

end Nilradical

end EnvelopingIsomorphism.Identification
