import Mathlib.LinearAlgebra.Finsupp.SumProd
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Isomorphisms

/-! The complementary block of a split basis is an actual basis of the quotient. -/

noncomputable section

namespace EnvelopingIsomorphism.LinearAlgebra

open Module

variable {R M α β : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (b : Basis (α ⊕ β) R M)

/-- Extract the complementary block of the coordinates in a split basis. -/
def complementaryCoordinates : M →ₗ[R] (β →₀ R) :=
  (LinearMap.snd R (α →₀ R) (β →₀ R)).comp
    ((Finsupp.sumFinsuppLEquivProdFinsupp R).toLinearMap.comp b.repr.toLinearMap)

@[simp] theorem complementaryCoordinates_apply (x : M) (i : β) :
    complementaryCoordinates b x i = b.repr x (.inr i) := rfl

@[simp] theorem complementaryCoordinates_basis_inl (i : α) :
    complementaryCoordinates b (b (.inl i)) = 0 := by
  classical
  ext j
  simp

@[simp] theorem complementaryCoordinates_basis_inr (i : β) :
    complementaryCoordinates b (b (.inr i)) = Finsupp.single i 1 := by
  classical
  ext j
  simp [Finsupp.single_apply]

theorem complementaryCoordinates_surjective : Function.Surjective (complementaryCoordinates b) := by
  intro p
  refine ⟨b.repr.symm ((Finsupp.sumFinsuppLEquivProdFinsupp R).symm (0, p)), ?_⟩
  simp [complementaryCoordinates]

theorem ker_complementaryCoordinates :
    LinearMap.ker (complementaryCoordinates b) = Submodule.span R (b '' Set.range Sum.inl) := by
  classical
  ext x
  rw [LinearMap.mem_ker, b.mem_span_image]
  constructor
  · intro hx i hi
    cases i with
    | inl i => exact ⟨i, rfl⟩
    | inr i =>
      have hz : b.repr x (.inr i) = 0 := by
        simpa only [complementaryCoordinates_apply, Finsupp.zero_apply] using
          congrArg (fun p : β →₀ R ↦ p i) hx
      exact (Finsupp.mem_support_iff.mp hi hz).elim
  · intro hx
    ext i
    rw [complementaryCoordinates_apply, Finsupp.zero_apply]
    by_contra hi
    obtain ⟨j, hj⟩ := hx (Finsupp.mem_support_iff.mpr hi)
    cases hj

variable (P : Submodule R M)
  (hspan : Submodule.span R (Set.range (fun i : α ↦ b (.inl i))) = P)

include hspan in
theorem ker_complementaryCoordinates_eq : LinearMap.ker (complementaryCoordinates b) = P := by
  rw [ker_complementaryCoordinates, ← Set.range_comp]
  exact hspan

/-- The quotient is linearly equivalent to free complementary coordinates. -/
def complementaryQuotientEquiv : (M ⧸ P) ≃ₗ[R] (β →₀ R) :=
  (Submodule.quotEquivOfEq _ _ (ker_complementaryCoordinates_eq b P hspan).symm).trans
    ((complementaryCoordinates b).quotKerEquivOfSurjective (complementaryCoordinates_surjective b))

@[simp] theorem complementaryQuotientEquiv_mk (x : M) :
    complementaryQuotientEquiv b P hspan (Submodule.Quotient.mk x) =
      complementaryCoordinates b x := by
  simp [complementaryQuotientEquiv]

/-- Complementary basis vectors descend to a basis of the actual module quotient. -/
def complementaryQuotientBasis : Basis β R (M ⧸ P) :=
  Finsupp.basisSingleOne.map (complementaryQuotientEquiv b P hspan).symm

@[simp] theorem complementaryQuotientBasis_apply (i : β) :
    complementaryQuotientBasis b P hspan i = Submodule.Quotient.mk (b (.inr i)) := by
  apply (complementaryQuotientEquiv b P hspan).injective
  simp [complementaryQuotientBasis]

include hspan in
/-- Freeness of this quotient is a conclusion, not an assumption. -/
theorem complementaryQuotient_free : Module.Free R (M ⧸ P) :=
  Module.Free.of_basis (complementaryQuotientBasis b P hspan)

end EnvelopingIsomorphism.LinearAlgebra
