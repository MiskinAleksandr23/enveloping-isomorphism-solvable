import EnvelopingIsomorphism.Enveloping.Injective
import EnvelopingIsomorphism.Identification.MetabelianBasic
import Mathlib.Data.Sum.Order

/-! Abelian ideals give genuine symmetric-algebra subalgebras of the native UEA. -/

noncomputable section

namespace EnvelopingIsomorphism.Enveloping

open UniversalEnvelopingAlgebra
open EnvelopingIsomorphism.Identification

attribute [local instance 100] LieRing.ofAssociativeRing

section Abelian

variable {R A : Type*} [CommRing R] [LieRing A] [LieAlgebra R A] [IsLieAbelian A]

theorem commute_enveloping_of_abelian (x y : UniversalEnvelopingAlgebra R A) : Commute x y := by
  have hy : y ∈ Algebra.adjoin R (Set.range (ι R (L := A))) := by
    rw [adjoin_range_ι]
    trivial
  apply Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy
  rintro _ ⟨b, rfl⟩
  apply Commute.symm
  have hx : x ∈ Algebra.adjoin R (Set.range (ι R (L := A))) := by
    rw [adjoin_range_ι]
    trivial
  apply Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx
  rintro _ ⟨a, rfl⟩
  change ι R b * ι R a = ι R a * ι R b
  rw [← sub_eq_zero, ← Ring.lie_def, ← LieHom.map_lie, trivial_lie_zero A A, map_zero]

/-- The existing ring structure is commutative for an abelian Lie algebra. -/
@[reducible] def abelianEnvelopingCommRing : CommRing (UniversalEnvelopingAlgebra R A) :=
  { (inferInstance : Ring (UniversalEnvelopingAlgebra R A)) with
    mul_comm := fun x y ↦ (commute_enveloping_of_abelian x y).eq }

attribute [local instance] abelianEnvelopingCommRing

/-- The generator map of the symmetric algebra is a Lie map when the Lie algebra is abelian. -/
def abelianSymmetricLieHom : A →ₗ⁅R⁆ SymmetricAlgebra R A where
  toLinearMap := SymmetricAlgebra.ι R A
  map_lie' {x y} := by
    change SymmetricAlgebra.ι R A ⁅x, y⁆ =
      ⁅SymmetricAlgebra.ι R A x, SymmetricAlgebra.ι R A y⁆
    rw [trivial_lie_zero A A, map_zero, Ring.lie_def, mul_comm, sub_self]

@[simp] theorem abelianSymmetricLieHom_apply (x : A) :
    abelianSymmetricLieHom (R := R) x = SymmetricAlgebra.ι R A x := rfl

/-- Algebra map from the symmetric algebra to an abelian enveloping algebra. -/
def abelianSymmetricToEnveloping :
    SymmetricAlgebra R A →ₐ[R] UniversalEnvelopingAlgebra R A :=
  SymmetricAlgebra.lift (ι R (L := A)).toLinearMap

@[simp] theorem abelianSymmetricToEnveloping_ι (x : A) :
    abelianSymmetricToEnveloping (SymmetricAlgebra.ι R A x) = ι R x :=
  SymmetricAlgebra.lift_ι_apply (ι R (L := A)).toLinearMap x

/-- Algebra map from an abelian enveloping algebra to the symmetric algebra. -/
def abelianEnvelopingToSymmetric :
    UniversalEnvelopingAlgebra R A →ₐ[R] SymmetricAlgebra R A :=
  UniversalEnvelopingAlgebra.lift R (abelianSymmetricLieHom (R := R) (A := A))

@[simp] theorem abelianEnvelopingToSymmetric_ι (x : A) :
    abelianEnvelopingToSymmetric (ι R x) = SymmetricAlgebra.ι R A x :=
  UniversalEnvelopingAlgebra.lift_ι_apply R abelianSymmetricLieHom x

/-- For an abelian Lie algebra the universal enveloping algebra is its
native Mathlib symmetric algebra, as an algebra. -/
def abelianSymmetricEquiv : SymmetricAlgebra R A ≃ₐ[R] UniversalEnvelopingAlgebra R A :=
  AlgEquiv.ofAlgHom abelianSymmetricToEnveloping abelianEnvelopingToSymmetric
    (by
      apply hom_ext_ι
      intro x
      change abelianSymmetricToEnveloping (abelianEnvelopingToSymmetric (ι R x)) = ι R x
      rw [abelianEnvelopingToSymmetric_ι, abelianSymmetricToEnveloping_ι])
    (by
      ext x
      change abelianEnvelopingToSymmetric
        (abelianSymmetricToEnveloping (SymmetricAlgebra.ι R A x)) =
          SymmetricAlgebra.ι R A x
      rw [abelianSymmetricToEnveloping_ι, abelianEnvelopingToSymmetric_ι])

@[simp] theorem abelianSymmetricEquiv_ι (x : A) :
    abelianSymmetricEquiv (SymmetricAlgebra.ι R A x) = ι R x := by
  exact abelianSymmetricToEnveloping_ι x

end Abelian

section Ideal

variable {k L : Type*} [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
  [FiniteDimensional k L] (H : LieIdeal k L)

omit [CharZero k] [FiniteDimensional k L] in
theorem range_map_idealIncl : (map H.incl).range = idealPolynomialPart H := by
  rw [map, range_lift]
  rfl

theorem map_idealIncl_injective : Function.Injective (map H.incl) :=
  map_injective H.incl Subtype.val_injective

/-- The enveloping algebra of the ideal is the actual generated subalgebra
inside the ambient enveloping algebra. -/
def idealEnvelopingEquiv : UniversalEnvelopingAlgebra k H ≃ₐ[k] idealPolynomialPart H :=
  (AlgEquiv.ofInjective (map H.incl) (map_idealIncl_injective H)).trans
    (Subalgebra.equivOfEq _ _ (range_map_idealIncl H))

@[simp] theorem idealEnvelopingEquiv_ι (x : H) :
    (idealEnvelopingEquiv H (ι k x) : UniversalEnvelopingAlgebra k L) = ι k (x : L) :=
  map_ι H.incl x

/-- The polynomial part of an abelian ideal is genuinely its symmetric algebra. -/
def idealPolynomialEquiv [IsLieAbelian H] :
    SymmetricAlgebra k H ≃ₐ[k] idealPolynomialPart H :=
  abelianSymmetricEquiv.trans (idealEnvelopingEquiv H)

@[simp] theorem idealPolynomialEquiv_ι [IsLieAbelian H] (x : H) :
    (idealPolynomialEquiv H (SymmetricAlgebra.ι k H x) : UniversalEnvelopingAlgebra k L) =
      ι k (x : L) := by
  change (idealEnvelopingEquiv H
    (abelianSymmetricEquiv (SymmetricAlgebra.ι k H x)) : UniversalEnvelopingAlgebra k L) = _
  rw [abelianSymmetricEquiv_ι, idealEnvelopingEquiv_ι]

end Ideal

section ZeroWeight

open EnvelopingIsomorphism.PBW

variable {R L α : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [LinearOrder α] (b : Module.Basis α R L) (H : LieIdeal R L)

theorem wordWeight_eq_zero_iff (ω : α → ℕ) (w : List α) :
    wordWeight ω w = 0 ↔ ∀ i ∈ w, ω i = 0 := by
  induction w with
  | nil => simp
  | cons i w ih => simp [wordWeight_cons, ih]

omit [LinearOrder α] in
theorem wordProduct_mem_idealPolynomialPart (w : List α)
    (hw : ∀ i ∈ w, b i ∈ H) :
    (w.map (ι R ∘ b)).prod ∈ idealPolynomialPart H := by
  induction w with
  | nil => exact one_mem _
  | cons i w ih =>
      exact mul_mem (ι_mem_idealPolynomialPart H (hw i (List.mem_cons_self ..)))
        (ih fun j hj ↦ hw j (List.mem_cons_of_mem i hj))

/-- In an adapted PBW basis, the actual ideal-generated algebra is exactly
the span of monomials having zero complementary weight. -/
theorem idealPolynomialPart_eq_weightedUpper_zero (ω : α → ℕ)
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → ω a ≤ ω i + ω j)
    (hH : (H : Submodule R L) = Submodule.span R (b '' {i | ω i = 0})) :
    (idealPolynomialPart H).toSubmodule = weightedUpper b ω 0 := by
  have hgen : ∀ x ∈ H, ι R x ∈ weightedUpper b ω 0 := by
    intro x hx
    change x ∈ (H : Submodule R L) at hx
    rw [hH] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, hi, rfl⟩ := hx
        change ω i = 0 at hi
        rw [← pbwBasis_single b i]
        exact pbwBasis_mem_weightedUpper b ω (by simp [Finsupp.weight_single, hi])
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx
  apply le_antisymm
  · intro x hx
    change x ∈ Algebra.adjoin R (Set.range (fun h : H ↦ ι R (h : L))) at hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨h, rfl⟩ := hx; exact hgen h h.property
    | algebraMap r =>
        rw [Algebra.algebraMap_eq_smul_one]
        apply Submodule.smul_mem
        rw [← pbwBasis_zero b]
        exact pbwBasis_mem_weightedUpper b ω (by simp)
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy =>
        exact weightedUpper_mul_le b ω hc 0 0 (Submodule.mul_mem_mul hx hy)
  · apply Submodule.span_le.mpr
    rintro _ ⟨m, hm, rfl⟩
    rw [pbwBasis_apply]
    apply wordProduct_mem_idealPolynomialPart b H
    have hw : wordWeight ω (orderedWord m) = 0 := by
      simpa only [wordWeight, wordIndex_orderedWord] using Nat.eq_zero_of_le_zero hm
    intro i hi
    change b i ∈ (H : Submodule R L)
    rw [hH]
    exact Submodule.subset_span ⟨i, (wordWeight_eq_zero_iff ω _).mp hw i hi, rfl⟩

end ZeroWeight

section AdaptedBasis

open EnvelopingIsomorphism.PBW

variable {R L α β : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [LinearOrder (α ⊕ β)] (b : Module.Basis (α ⊕ β) R L) (H : LieIdeal R L)

/-- Complementary degree: ideal basis letters have weight zero and the
chosen complementary letters have weight one. -/
def complementWeight : α ⊕ β → ℕ := Sum.elim (fun _ ↦ 0) (fun _ ↦ 1)

omit [LinearOrder (α ⊕ β)] in
theorem complementWeight_bracket_bound [IsLieAbelian H]
    (hH : (H : Submodule R L) = Submodule.span R (Set.range (fun i : α ↦ b (.inl i)))) :
    ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 →
      complementWeight a ≤ complementWeight i + complementWeight j := by
  have hb (i : α) : b (.inl i) ∈ H := by
    change b (.inl i) ∈ (H : Submodule R L)
    rw [hH]
    exact Submodule.subset_span ⟨i, rfl⟩
  intro i j a hcoeff
  cases i with
  | inr i => cases j <;> cases a <;> simp [complementWeight]
  | inl i =>
      cases j with
      | inr j => cases a <;> simp [complementWeight]
      | inl j =>
          have hzero : ⁅b (.inl i), b (.inl j)⁆ = 0 :=
            congrArg (fun x : H ↦ (x : L))
              (trivial_lie_zero H H ⟨b (.inl i), hb i⟩ ⟨b (.inl j), hb j⟩)
          exact (hcoeff (by simp [hzero])).elim

/-- For an ideal-first adapted basis, the actual polynomial part consists
exactly of PBW monomials of complementary degree zero. -/
theorem idealPolynomialPart_eq_complementDegree_zero [IsLieAbelian H]
    (hH : (H : Submodule R L) = Submodule.span R (Set.range (fun i : α ↦ b (.inl i)))) :
    (idealPolynomialPart H).toSubmodule = weightedUpper b complementWeight 0 := by
  have hset : b '' {i | complementWeight i = 0} =
      Set.range (fun i : α ↦ b (.inl i)) := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      cases i with
      | inl i => exact ⟨i, rfl⟩
      | inr i => simp [complementWeight] at hi
    · rintro ⟨i, rfl⟩
      exact ⟨.inl i, rfl, rfl⟩
  apply idealPolynomialPart_eq_weightedUpper_zero b H complementWeight
    (complementWeight_bracket_bound b H hH)
  simpa only [hset] using hH

end AdaptedBasis

/-- A linear order on an ordinary sum type placing all ideal indices before
all complementary indices. -/
@[reducible] def idealFirstOrder (α β : Type*) [LinearOrder α] [LinearOrder β] :
    LinearOrder (α ⊕ β) :=
  LinearOrder.lift' (toLex : (α ⊕ β) ≃ Lex (α ⊕ β)) toLex.injective

/-- Every ideal in a finite-dimensional Lie algebra admits a basis split
into an ideal block and a complementary block. -/
theorem exists_idealAdaptedBasis {k L : Type*} [Field k] [LieRing L] [LieAlgebra k L]
    [FiniteDimensional k L] (H : LieIdeal k L) :
    ∃ (n m : ℕ) (b : Module.Basis (Fin n ⊕ Fin m) k L),
      (H : Submodule k L) = Submodule.span k (Set.range (fun i : Fin n ↦ b (.inl i))) := by
  let p : Submodule k L := H
  obtain ⟨q, hpq⟩ := p.exists_isCompl
  let bp := Module.finBasis k p
  let bq := Module.finBasis k q
  let b := (bp.prod bq).map (p.prodEquivOfIsCompl q hpq)
  refine ⟨Module.finrank k p, Module.finrank k q, b, ?_⟩
  have hb (i) : b (.inl i) = (bp i : L) := by
    simp [b, Module.Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']
  have hmap := congrArg (Submodule.map p.subtype) bp.span_eq
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at hmap
  simpa only [hb, Function.comp_def, Submodule.subtype_apply] using hmap.symm

end EnvelopingIsomorphism.Enveloping
