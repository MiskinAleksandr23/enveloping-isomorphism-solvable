import EnvelopingIsomorphism.PBW.Symmetrization

/-! Ordinary PBW degree is preserved in both directions by the actual symmetrization equivalence. -/

noncomputable section

namespace EnvelopingIsomorphism.PBW

section TriangularFiltration

variable {R ι : Type*} [CommRing R]
  (d : ι → ℕ) (T : Module.End R (ι →₀ R))
  (hT : ∀ i, T (Finsupp.single i 1) - Finsupp.single i 1 ∈
    Finsupp.supported R R {j | d j < d i})

include hT

theorem triangular_remainder_mem_supported {p : ι →₀ R} {n : ℕ}
    (hp : p ∈ Finsupp.supported R R {i | d i ≤ n}) :
    T p - p ∈ Finsupp.supported R R {i | d i < n} := by
  have hmap : Finsupp.supported R R {i | d i ≤ n} ≤
      (Finsupp.supported R R {i | d i < n}).comap (T - 1) := by
    rw [Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    change T (Finsupp.single i 1) - Finsupp.single i 1 ∈
      Finsupp.supported R R {i | d i < n}
    apply Finsupp.supported_mono (M := R) (R := R) _ (hT i)
    intro j hj
    change d j < d i at hj
    change d i ≤ n at hi
    exact lt_of_lt_of_le hj hi
  exact hmap hp

/-- A unitriangular coordinate map preserves each finite degree bound. -/
theorem triangular_mem_supported {p : ι →₀ R} {n : ℕ}
    (hp : p ∈ Finsupp.supported R R {i | d i ≤ n}) :
    T p ∈ Finsupp.supported R R {i | d i ≤ n} := by
  have hrem := triangular_remainder_mem_supported d T hT hp
  have hrem' : T p - p ∈ Finsupp.supported R R {i | d i ≤ n} :=
    Finsupp.supported_mono (M := R) (R := R) (by
      intro i hi
      change d i ≤ n
      exact (show d i < n from hi).le) hrem
  simpa only [sub_add_cancel] using Submodule.add_mem _ hrem' hp

/-- The top nonzero coordinate cannot disappear under a unitriangular map.
This proves inverse filteredness without presupposing a filtered inverse. -/
theorem mem_supported_of_triangular_mem {p : ι →₀ R} {n : ℕ}
    (hp : T p ∈ Finsupp.supported R R {i | d i ≤ n}) :
    p ∈ Finsupp.supported R R {i | d i ≤ n} := by
  classical
  let N := p.support.sup d
  have hpN : p ∈ Finsupp.supported R R {i | d i ≤ N} := by
    intro i hi
    exact (show d i ≤ p.support.sup d from Finset.le_sup hi)
  have hrem := triangular_remainder_mem_supported d T hT hpN
  intro i hi
  obtain ⟨j, hj, hmax⟩ := Finset.exists_mem_eq_sup p.support ⟨i, hi⟩ d
  have hz : (T p - p) j = 0 :=
    (Finsupp.mem_supported' R _).mp hrem j (by
      change ¬ d j < N
      rw [show N = d j from hmax]
      exact lt_irrefl _)
  have heq : T p j = p j := sub_eq_zero.mp hz
  have hjT : j ∈ (T p).support := by
    rw [Finsupp.mem_support_iff, heq]
    exact Finsupp.mem_support_iff.mp hj
  calc
    d i ≤ p.support.sup d := Finset.le_sup hi
    _ = d j := hmax
    _ ≤ n := hp hjT

theorem triangular_mem_supported_iff (p : ι →₀ R) (n : ℕ) :
    T p ∈ Finsupp.supported R R {i | d i ≤ n} ↔
      p ∈ Finsupp.supported R R {i | d i ≤ n} :=
  ⟨mem_supported_of_triangular_mem d T hT, triangular_mem_supported d T hT⟩

end TriangularFiltration

section Symmetrization

variable {R L α : Type*} [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LinearOrder α] (b : Module.Basis α R L)

theorem symmetrizationCoordinates_mem_supported_iff (p : (α →₀ ℕ) →₀ R) (n : ℕ) :
    symmetrizationCoordinates b p ∈ Finsupp.supported R R {m | m.degree ≤ n} ↔
      p ∈ Finsupp.supported R R {m | m.degree ≤ n} := by
  apply triangular_mem_supported_iff Finsupp.degree (symmetrizationCoordinates b)
  intro m
  rw [symmetrizationCoordinates_single]
  simpa only [length_orderedWord, Finsupp.degree_apply, Finsupp.sum] using
    symmetrization_basis_sub_mem_supported b m

theorem symmetrizationCoordinates_repr (x : SymmetricAlgebra R L) :
    symmetrizationCoordinates b (b.symmetricAlgebra.repr x) =
      (pbwBasis b).repr (symmetrizationEquiv b x) := by
  simp only [symmetrizationCoordinates, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, symmetrizationEquiv_apply]

/-- The true symmetrization map preserves and reflects the ordinary PBW filtration. -/
theorem symmetrizationEquiv_mem_weightedUpper_iff (x : SymmetricAlgebra R L) (n : ℕ) :
    symmetrizationEquiv b x ∈ weightedUpper b (fun _ ↦ 1) n ↔
      ∀ m ∈ (b.symmetricAlgebra.repr x).support, m.degree ≤ n := by
  have h := symmetrizationCoordinates_mem_supported_iff b (b.symmetricAlgebra.repr x) n
  rw [symmetrizationCoordinates_repr] at h
  rw [mem_weightedUpper_iff]
  simp only [Finsupp.mem_supported, Set.subset_def, Finset.mem_coe, Set.mem_setOf_eq] at h
  simpa only [Finsupp.degree_eq_weight_one] using h

/-- Actual inverse symmetrization cannot raise ordinary degree. -/
theorem symmetrizationEquiv_symm_support_degree_le {x : UniversalEnvelopingAlgebra R L} {n : ℕ}
    (hx : x ∈ weightedUpper b (fun _ ↦ 1) n) {m : α →₀ ℕ}
    (hm : m ∈ (b.symmetricAlgebra.repr ((symmetrizationEquiv b).symm x)).support) :
    m.degree ≤ n := by
  have h := (symmetrizationEquiv_mem_weightedUpper_iff b ((symmetrizationEquiv b).symm x) n).mp
    (by simpa only [LinearEquiv.apply_symm_apply] using hx)
  exact h m hm

/-- The same inverse bound in the standard native multivariate polynomial coordinates. -/
theorem symmetrizationEquiv_symm_polynomial_support_degree_le
    {x : UniversalEnvelopingAlgebra R L} {n : ℕ}
    (hx : x ∈ weightedUpper b (fun _ ↦ 1) n) {m : α →₀ ℕ}
    (hm : m ∈ ((SymmetricAlgebra.equivMvPolynomial b) ((symmetrizationEquiv b).symm x)).support) :
    m.degree ≤ n :=
  symmetrizationEquiv_symm_support_degree_le b hx hm

/-- The forward filteredness statement, without any finiteness assumption on the basis. -/
theorem symmetrizationEquiv_mem_weightedUpper (x : SymmetricAlgebra R L) (n : ℕ)
    (hx : ∀ m ∈ (b.symmetricAlgebra.repr x).support, m.degree ≤ n) :
    symmetrizationEquiv b x ∈ weightedUpper b (fun _ ↦ 1) n :=
  (symmetrizationEquiv_mem_weightedUpper_iff b x n).mpr hx

end Symmetrization

end EnvelopingIsomorphism.PBW
