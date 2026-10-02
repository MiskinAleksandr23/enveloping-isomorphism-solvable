import Mathlib.RingTheory.Nullstellensatz
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois.GaloisClosure

/-! Polynomial equations with a point over any extension have a point over a finite Galois field. -/

noncomputable section

namespace EnvelopingIsomorphism.FieldTheory

variable {k E Ω σ : Type*} [Field k] [Field E] [Algebra k E]
  [Field Ω] [Algebra k Ω]

/-- A field-valued point makes its ideal of equations proper, even for transcendental extensions. -/
theorem ideal_ne_top_of_point (J : Ideal (MvPolynomial σ k)) (x : σ → E)
    (hx : ∀ p ∈ J, MvPolynomial.aeval x p = 0) : J ≠ ⊤ := by
  intro hJ
  have h := hx 1 (by rw [hJ]; trivial)
  simp at h

/-- A proper ideal in finitely many variables has a point in any algebraically closed extension. -/
theorem exists_point_of_proper [Finite σ] [IsAlgClosed Ω]
    (J : Ideal (MvPolynomial σ k)) (hJ : J ≠ ⊤) :
    ∃ x : σ → Ω, ∀ p ∈ J, MvPolynomial.aeval x p = 0 := by
  obtain ⟨P, hP, hJP⟩ := Ideal.exists_le_maximal J hJ
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal Ω hP
  refine ⟨x, fun p hp ↦ ?_⟩
  have hmem : p ∈ MvPolynomial.vanishingIdeal k {x} := hx ▸ hJP hp
  exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x p).mp hmem

/-- Polynomial evaluation commutes with inclusion of an intermediate field. -/
theorem aeval_intermediateField_coe (K : IntermediateField k Ω) (y : σ → K)
    (p : MvPolynomial σ k) :
    (MvPolynomial.aeval y p : Ω) = MvPolynomial.aeval (fun i ↦ (y i : Ω)) p :=
  MvPolynomial.comp_aeval_apply y K.val p

/-- The ambient inclusion reflects the exact polynomial equations. -/
theorem aeval_eq_zero_iff_coe (K : IntermediateField k Ω) (y : σ → K)
    (p : MvPolynomial σ k) :
    MvPolynomial.aeval y p = 0 ↔ MvPolynomial.aeval (fun i ↦ (y i : Ω)) p = 0 := by
  constructor
  · intro h
    rw [← aeval_intermediateField_coe K y p, h]
    rfl
  · intro h
    apply Subtype.val_injective
    change (MvPolynomial.aeval y p : Ω) = 0
    rwa [aeval_intermediateField_coe]

section GaloisCoordinates

variable [Finite σ] [IsGalois k Ω]

/-- The finite Galois intermediate field generated normally by a finite tuple of coordinates. -/
def coordinateGaloisField (x : σ → Ω) : FiniteGaloisIntermediateField k Ω := by
  letI : Finite (Set.range x) := (Set.finite_range x).to_subtype
  exact FiniteGaloisIntermediateField.adjoin k (Set.range x)

theorem mem_coordinateGaloisField (x : σ → Ω) (i : σ) :
    x i ∈ (coordinateGaloisField (k := k) x).toIntermediateField := by
  letI : Finite (Set.range x) := (Set.finite_range x).to_subtype
  exact FiniteGaloisIntermediateField.subset_adjoin k (Set.range x) ⟨i, rfl⟩

/-- The same tuple, now valued in its actual finite Galois coefficient field. -/
def coordinatePoint (x : σ → Ω) : σ → coordinateGaloisField (k := k) x :=
  fun i ↦ ⟨x i, mem_coordinateGaloisField x i⟩

@[simp] theorem coordinatePoint_coe (x : σ → Ω) (i : σ) :
    (coordinatePoint (k := k) x i : Ω) = x i := rfl

theorem coordinatePoint_aeval_eq_zero (x : σ → Ω) (p : MvPolynomial σ k) :
    MvPolynomial.aeval (coordinatePoint (k := k) x) p = 0 ↔ MvPolynomial.aeval x p = 0 :=
  aeval_eq_zero_iff_coe _ _ _

end GaloisCoordinates

section AlgebraicClosure

variable [CharZero k] [Finite σ]

/-- A proper finite-variable ideal has a point over a finite Galois intermediate field
of the fixed algebraic closure. No rational-point descent is asserted. -/
theorem exists_finiteGaloisPoint_of_proper (J : Ideal (MvPolynomial σ k)) (hJ : J ≠ ⊤) :
    ∃ K : FiniteGaloisIntermediateField k (AlgebraicClosure k),
      ∃ y : σ → K, ∀ p ∈ J, MvPolynomial.aeval y p = 0 := by
  letI : IsGalois k (AlgebraicClosure k) := ⟨⟩
  obtain ⟨x, hx⟩ := exists_point_of_proper (Ω := AlgebraicClosure k) J hJ
  refine ⟨coordinateGaloisField x, coordinatePoint x, ?_⟩
  intro p hp
  exact (coordinatePoint_aeval_eq_zero x p).mpr (hx p hp)

/-- An arbitrary extension-valued point produces a finite Galois point of the same equations. -/
theorem exists_finiteGaloisPoint_of_point (J : Ideal (MvPolynomial σ k)) (x : σ → E)
    (hx : ∀ p ∈ J, MvPolynomial.aeval x p = 0) :
    ∃ K : FiniteGaloisIntermediateField k (AlgebraicClosure k),
      ∃ y : σ → K, ∀ p ∈ J, MvPolynomial.aeval y p = 0 :=
  exists_finiteGaloisPoint_of_proper J (ideal_ne_top_of_point J x hx)

theorem exists_finiteGaloisPoint (J : Ideal (MvPolynomial σ k))
    (h : ∃ x : σ → E, ∀ p ∈ J, MvPolynomial.aeval x p = 0) :
    ∃ K : FiniteGaloisIntermediateField k (AlgebraicClosure k),
      ∃ y : σ → K, ∀ p ∈ J, MvPolynomial.aeval y p = 0 := by
  obtain ⟨x, hx⟩ := h
  exact exists_finiteGaloisPoint_of_point J x hx

theorem exists_finiteGalois_zeroLocus (J : Ideal (MvPolynomial σ k))
    (h : (MvPolynomial.zeroLocus E J).Nonempty) :
    ∃ K : FiniteGaloisIntermediateField k (AlgebraicClosure k),
      (MvPolynomial.zeroLocus K J).Nonempty := by
  obtain ⟨K, y, hy⟩ := exists_finiteGaloisPoint J h
  exact ⟨K, y, hy⟩

/-- The corresponding statement for an explicitly supplied family of polynomial equations. -/
theorem exists_finiteGaloisPoint_of_equations (S : Set (MvPolynomial σ k)) (x : σ → E)
    (hx : ∀ p ∈ S, MvPolynomial.aeval x p = 0) :
    ∃ K : FiniteGaloisIntermediateField k (AlgebraicClosure k),
      ∃ y : σ → K, ∀ p ∈ S, MvPolynomial.aeval y p = 0 := by
  have hker : Ideal.span S ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom := by
    apply Ideal.span_le.mpr
    exact hx
  obtain ⟨K, y, hy⟩ := exists_finiteGaloisPoint_of_point (Ideal.span S) x
    (fun p hp ↦ hker hp)
  exact ⟨K, y, fun p hp ↦ hy p (Ideal.subset_span hp)⟩

end AlgebraicClosure

end EnvelopingIsomorphism.FieldTheory
