import EnvelopingIsomorphism.Identification.Metabelian
import EnvelopingIsomorphism.Enveloping.AbelianIdeal

/-! The affine polynomial part is locally finite: the easy LF inclusion of HQ2. -/

noncomputable section
namespace EnvelopingIsomorphism.Identification

open UniversalEnvelopingAlgebra EnvelopingIsomorphism.PBW
open EnvelopingIsomorphism.Enveloping (complementWeight)
attribute [local instance 100] LieRing.ofAssociativeRing

variable {R L α β : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [LinearOrder (α ⊕ β)] (b : Module.Basis (α ⊕ β) R L) (H : LieIdeal R L)
  [IsLieAbelian H]
  (hH : (H : Submodule R L) = Submodule.span R (Set.range (fun i : α => b (.inl i))))

def affineWeight (d : ℕ) : α ⊕ β → ℕ := Sum.elim (fun _ => 1) (fun _ => d + 1)

include hH in
omit [LinearOrder (α ⊕ β)] [IsLieAbelian H] in
theorem basisSupport_ideal : (H : Submodule R L) = basisSupport b (Set.range Sum.inl) := by
  rw [hH, basisSupport, ← Set.range_comp]
  rfl

include hH in
omit [LinearOrder (α ⊕ β)] [IsLieAbelian H] in
theorem ideal_basis_mem (i : α) : b (.inl i) ∈ H := by
  change b (.inl i) ∈ (H : Submodule R L)
  rw [basisSupport_ideal b H hH]
  exact basis_mem_basisSupport b ⟨i, rfl⟩

include hH in
omit [LinearOrder (α ⊕ β)] [IsLieAbelian H] in
theorem coeff_eq_zero_on_complement {x : L} (hx : x ∈ H) (j : β) :
    b.repr x (.inr j) = 0 := by
  by_contra hc
  change x ∈ (H : Submodule R L) at hx
  rw [basisSupport_ideal b H hH] at hx
  obtain ⟨i, hi⟩ := (mem_basisSupport b _ x).mp hx (.inr j) (Finsupp.mem_support_iff.mpr hc)
  cases hi

include hH in
omit [LinearOrder (α ⊕ β)] in
/-- Complementary PBW weights strictly drop in every nonzero Lie bracket
for an abelian ideal, including an arbitrary extension cocycle. -/
theorem complementWeight_bracket_strict :
    ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 →
      complementWeight a < complementWeight i + complementWeight j := by
  intro i j a hcoeff
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hz : ⁅b (.inl i), b (.inl j)⁆ = 0 := congrArg (fun x : H => (x : L))
        (trivial_lie_zero H H ⟨b (.inl i), ideal_basis_mem b H hH i⟩
          ⟨b (.inl j), ideal_basis_mem b H hH j⟩)
      exact (hcoeff (by simp [hz])).elim
    | inr j =>
      cases a with
      | inl a => simp [complementWeight]
      | inr a => exact (hcoeff (coeff_eq_zero_on_complement b H hH
          (lie_mem_left R L H _ _ (ideal_basis_mem b H hH i)) a)).elim
  | inr i =>
    cases j with
    | inl j =>
      cases a with
      | inl a => simp [complementWeight]
      | inr a => exact (hcoeff (coeff_eq_zero_on_complement b H hH
          (H.lie_mem (ideal_basis_mem b H hH j)) a)).elim
    | inr j => cases a <;> simp [complementWeight]

include hH in
omit [LinearOrder (α ⊕ β)] in
theorem affineWeight_bracket_bound (d : ℕ) :
    ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 →
      affineWeight d a ≤ affineWeight d i + affineWeight d j := by
  intro i j a hcoeff
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hz : ⁅b (.inl i), b (.inl j)⁆ = 0 := congrArg (fun x : H => (x : L))
        (trivial_lie_zero H H ⟨b (.inl i), ideal_basis_mem b H hH i⟩
          ⟨b (.inl j), ideal_basis_mem b H hH j⟩)
      exact (hcoeff (by simp [hz])).elim
    | inr j => cases a <;> simp [affineWeight]
  | inr i =>
    cases j <;> cases a <;> simp [affineWeight]
    omega

omit [LinearOrder (α ⊕ β)] in
theorem affineWeight_pos (d : ℕ) (i : α ⊕ β) : affineWeight d i ≠ 0 := by
  cases i <;> simp [affineWeight]

omit [LinearOrder (α ⊕ β)] in
theorem affineWeight_le (d : ℕ) (i : α ⊕ β) : affineWeight d i ≤ d + 1 := by
  cases i <;> simp [affineWeight]

omit [LinearOrder (α ⊕ β)] in
theorem affine_weight_eq_ordinary_of_complement_zero (d : ℕ) (m : (α ⊕ β) →₀ ℕ)
    (hm : Finsupp.weight complementWeight m = 0) :
    Finsupp.weight (affineWeight d) m = Finsupp.weight (fun _ => 1) m := by
  classical
  rw [Finsupp.weight_apply, Finsupp.weight_apply]
  apply Finsupp.sum_congr
  intro i hi
  cases i with
  | inl i => rfl
  | inr i =>
    have h := Finsupp.le_weight_of_ne_zero' complementWeight (Finsupp.mem_support_iff.mp hi)
    rw [hm] at h
    change 1 ≤ 0 at h
    omega

include hH in
theorem polynomialPart_mem_affineUpper_of_ordinary
    (d : ℕ) {p : UniversalEnvelopingAlgebra R L}
    (hp : p ∈ idealPolynomialPart H) (hdeg : p ∈ weightedUpper b (fun _ => 1) d) :
    p ∈ weightedUpper b (affineWeight d) d := by
  have hp0 : p ∈ weightedUpper b complementWeight 0 := by
    rw [← EnvelopingIsomorphism.Enveloping.idealPolynomialPart_eq_complementDegree_zero b H hH]
    exact hp
  apply (mem_weightedUpper_iff b _ _ p).mpr
  intro m hm
  have hm0 := (mem_weightedUpper_iff b complementWeight 0 p).mp hp0 m hm
  rw [affine_weight_eq_ordinary_of_complement_zero d m (Nat.eq_zero_of_le_zero hm0)]
  exact (mem_weightedUpper_iff b _ _ p).mp hdeg m hm

theorem ι_mem_affineUpper (d : ℕ) (x : L) :
    ι R x ∈ weightedUpper b (affineWeight d) (d + 1) := by
  have hspan : Submodule.span R (Set.range b) ≤
      (weightedUpper b (affineWeight d) (d + 1)).comap (ι R).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change ι R (b i) ∈ weightedUpper b (affineWeight d) (d + 1)
    rw [← pbwBasis_single b i]
    apply pbwBasis_mem_weightedUpper
    simpa only [Finsupp.weight_single, one_nsmul] using affineWeight_le d i
  rw [b.span_eq] at hspan
  exact hspan (Submodule.mem_top : x ∈ (⊤ : Submodule R L))

include hH in
omit [IsLieAbelian H] in
theorem ι_ideal_mem_affineUpper_one (d : ℕ) {x : L} (hx : x ∈ H) :
    ι R x ∈ weightedUpper b (affineWeight d) 1 := by
  change x ∈ (H : Submodule R L) at hx
  rw [hH] at hx
  have hspan : Submodule.span R (Set.range (fun i : α => b (.inl i))) ≤
      (weightedUpper b (affineWeight d) 1).comap (ι R).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change ι R (b (.inl i)) ∈ weightedUpper b (affineWeight d) 1
    rw [← pbwBasis_single b (.inl i)]
    apply pbwBasis_mem_weightedUpper
    simp [Finsupp.weight_single, affineWeight]
  exact hspan hx

include hH in
/-- For an abelian ideal, every sum of a linear Lie element and a polynomial
in that ideal has locally finite inner derivation. -/
theorem affine_idealPolynomialPart_mem_LF [Finite α] [Finite β] [IsNoetherianRing R]
    (x : L) {p : UniversalEnvelopingAlgebra R L} (hp : p ∈ idealPolynomialPart H) :
    ι R x + p ∈ LF R (UniversalEnvelopingAlgebra R L) := by
  obtain ⟨d, hd⟩ := exists_mem_weightedUpper b (fun _ => 1) p
  have hderiv (y : L) : ⁅ι R y, p⁆ ∈ weightedUpper b (affineWeight d) d := by
    apply polynomialPart_mem_affineUpper_of_ordinary b H hH d
      (lie_mem_idealPolynomialPart H y hp)
    apply lie_mem_weightedUpper_of_generator_bound b (fun _ => 1)
      (by intros; omega) (ι R y) _ hd
    intro i
    rw [← LieHom.map_lie]
    exact ι_mem_ordinaryUpper_one b ⁅y, b i⁆
  apply mem_LF_of_weighted_generator_bound b (affineWeight d) (affineWeight_pos d)
    (affineWeight_bracket_bound b H hH d) (ι R x + p)
  intro i
  rw [add_lie, ← LieHom.map_lie]
  cases i with
  | inl i =>
    have hzero : ⁅p, ι R (b (.inl i))⁆ = 0 :=
      lie_eq_zero_of_mem_idealPolynomialPart H hp
        (ι_mem_idealPolynomialPart H (ideal_basis_mem b H hH i))
    rw [hzero, add_zero]
    exact ι_ideal_mem_affineUpper_one b H hH d (H.lie_mem (ideal_basis_mem b H hH i))
  | inr i =>
    apply add_mem (ι_mem_affineUpper b d ⁅x, b (.inr i)⁆)
    rw [← lie_skew p (ι R (b (.inr i)))]
    apply neg_mem
    exact weightedUpper_mono b (affineWeight d) (Nat.le_succ d) (hderiv (b (.inr i)))

section WithoutBasis

variable {k M : Type*} [Field k] [LieRing M] [LieAlgebra k M] [Module.Finite k M]

/-- Basis-free easy LF inclusion for an arbitrary finite-dimensional algebra
and an abelian ideal. The adapted basis is constructed, not assumed. -/
theorem linear_add_idealPolynomialPart_mem_LF (I : LieIdeal k M) [IsLieAbelian I]
    (x : M) {p : UniversalEnvelopingAlgebra k M} (hp : p ∈ idealPolynomialPart I) :
    ι k x + p ∈ LF k (UniversalEnvelopingAlgebra k M) := by
  obtain ⟨n, m, b, hb⟩ := EnvelopingIsomorphism.Enveloping.exists_idealAdaptedBasis I
  letI := EnvelopingIsomorphism.Enveloping.idealFirstOrder (Fin n) (Fin m)
  exact affine_idealPolynomialPart_mem_LF b I hb x hp

end WithoutBasis
end EnvelopingIsomorphism.Identification
