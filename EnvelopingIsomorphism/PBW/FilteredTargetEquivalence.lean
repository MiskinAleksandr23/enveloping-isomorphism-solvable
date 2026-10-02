import EnvelopingIsomorphism.PBW.SymmetrizationFiltration
import EnvelopingIsomorphism.Enveloping.UniversalProperties

/-!
# The enveloping algebra of a triangular associative target

An actual associative algebra with a monomial basis and triangular generator
multiplication is canonically isomorphic to the native enveloping algebra.
Associativity and the Lie-generator relations are inputs; bijectivity is proved.
-/

noncomputable section

namespace EnvelopingIsomorphism.PBW.FilteredTargetEquivalence

open Finsupp
open UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R L B α : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [Ring B] [Algebra R B] [LinearOrder α]
  (b : Module.Basis α R L) (c : Module.Basis (α →₀ ℕ) R B) (g : L →ₗ⁅R⁆ B)

/-- Multiplying a target monomial by one generator has the ordinary monomial
as leading term and only terms of strictly lower ordinary degree. -/
def GeneratorTriangular : Prop := ∀ i m,
  c.repr (g (b i) * c m) - Finsupp.single (Finsupp.single i 1 + m) 1 ∈
    Finsupp.supported R R {q | q.degree < m.degree + 1}

/-- Left generator multiplication in the chosen target coordinates. -/
def generatorCoordinates (i : α) : Module.End R ((α →₀ ℕ) →₀ R) :=
  c.repr.toLinearMap.comp
    ((LinearMap.mulLeft R (g (b i))).comp c.repr.symm.toLinearMap)

omit [LinearOrder α] in
theorem generatorCoordinates_apply (i : α) (p : (α →₀ ℕ) →₀ R) :
    generatorCoordinates b c g i p = c.repr (g (b i) * c.repr.symm p) := rfl

omit [LinearOrder α] in
@[simp] theorem generatorCoordinates_single (i : α) (m : α →₀ ℕ) (r : R) :
    generatorCoordinates b c g i (Finsupp.single m r) = r • c.repr (g (b i) * c m) := by
  simp [generatorCoordinates]

omit [LinearOrder α] in
/-- Generator multiplication raises an existing strict degree bound by at most one. -/
theorem generatorCoordinates_mem_supported (htri : GeneratorTriangular b c g)
    (i : α) {p : (α →₀ ℕ) →₀ R} {d : ℕ}
    (hp : p ∈ Finsupp.supported R R {m | m.degree < d}) :
    generatorCoordinates b c g i p ∈ Finsupp.supported R R {m | m.degree < d + 1} := by
  rw [Finsupp.supported_eq_span_single] at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨m, hm, rfl⟩ := hp
      rw [generatorCoordinates_single, one_smul]
      have hrem : c.repr (g (b i) * c m) - Finsupp.single (Finsupp.single i 1 + m) 1 ∈
          Finsupp.supported R R {q | q.degree < d + 1} := by
        apply Finsupp.supported_mono (M := R) (R := R) _ (htri i m)
        intro q hq
        change m.degree < d at hm
        change q.degree < m.degree + 1 at hq
        change q.degree < d + 1
        omega
      have hsingle : Finsupp.single (Finsupp.single i 1 + m) (1 : R) ∈
          Finsupp.supported R R {q | q.degree < d + 1} := by
        apply Finsupp.single_mem_supported
        change (Finsupp.single i 1 + m).degree < d + 1
        simp only [map_add, Finsupp.degree_single]
        change m.degree < d at hm
        omega
      simpa only [sub_add_cancel] using Submodule.add_mem _ hrem hsingle
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

theorem wordIndex_degree (w : List α) : (wordIndex w).degree = w.length := by
  simpa only [Finsupp.degree_apply, Finsupp.sum] using wordIndex_sum w

/-- The actual target product of any word has its expected commutative monomial
as leading coordinate. This is derived from one-generator multiplication. -/
theorem word_product_triangular (hunit : c 0 = 1) (htri : GeneratorTriangular b c g)
    (w : List α) :
    c.repr ((w.map (g ∘ b)).prod) - Finsupp.single (wordIndex w) 1 ∈
      Finsupp.supported R R {q | q.degree < w.length} := by
  induction w with
  | nil =>
      simp only [List.map_nil, List.prod_nil, wordIndex_nil, ← hunit,
        Module.Basis.repr_self, sub_self]
      exact zero_mem _
  | cons i w ih =>
      have hmul := generatorCoordinates_mem_supported b c g htri i ih
      have hrem := htri i (wordIndex w)
      rw [wordIndex_degree] at hrem
      have hsum := Submodule.add_mem
        (Finsupp.supported R R {q : α →₀ ℕ | q.degree < w.length + 1}) hmul hrem
      simp only [List.map_cons, List.prod_cons, Function.comp_apply,
        wordIndex_cons, List.length_cons]
      convert hsum using 1
      rw [map_sub, generatorCoordinates_apply, generatorCoordinates_single, one_smul,
        LinearEquiv.symm_apply_apply]
      abel

/-- Coordinates of the canonical algebra homomorphism induced by the Lie generators. -/
def canonicalCoordinates : Module.End R ((α →₀ ℕ) →₀ R) :=
  c.repr.toLinearMap.comp
    ((UniversalEnvelopingAlgebra.lift R g).toLinearMap.comp (pbwBasis b).repr.symm.toLinearMap)

@[simp] theorem canonicalCoordinates_single (m : α →₀ ℕ) :
    canonicalCoordinates b c g (Finsupp.single m 1) =
      c.repr (UniversalEnvelopingAlgebra.lift R g (pbwBasis b m)) := by
  simp [canonicalCoordinates]

theorem lift_pbwBasis (m : α →₀ ℕ) :
    UniversalEnvelopingAlgebra.lift R g (pbwBasis b m) =
      ((orderedWord m).map (g ∘ b)).prod := by
  rw [pbwBasis_apply, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact UniversalEnvelopingAlgebra.lift_ι_apply R g (b i)

theorem canonicalCoordinates_triangular (hunit : c 0 = 1)
    (htri : GeneratorTriangular b c g) (m : α →₀ ℕ) :
    canonicalCoordinates b c g (Finsupp.single m 1) - Finsupp.single m 1 ∈
      Finsupp.supported R R {q | q.degree < m.degree} := by
  rw [canonicalCoordinates_single, lift_pbwBasis]
  have h := word_product_triangular b c g hunit htri (orderedWord m)
  simpa only [wordIndex_orderedWord, length_orderedWord, Finsupp.degree_apply, Finsupp.sum] using h

/-- The canonical coordinate map is bijective by the finite degree-lowering inverse. -/
theorem canonicalCoordinates_bijective (hunit : c 0 = 1)
    (htri : GeneratorTriangular b c g) : Function.Bijective (canonicalCoordinates b c g) :=
  bijective_of_degree_triangular Finsupp.degree (canonicalCoordinates b c g)
    (canonicalCoordinates_triangular b c g hunit htri)

theorem canonicalCoordinates_repr (x : UniversalEnvelopingAlgebra R L) :
    canonicalCoordinates b c g ((pbwBasis b).repr x) =
      c.repr (UniversalEnvelopingAlgebra.lift R g x) := by
  simp [canonicalCoordinates]

/-- Bijectivity of the actual universal algebra homomorphism is a consequence
of triangular generator multiplication, rather than an assumption. -/
theorem lift_bijective (hunit : c 0 = 1) (htri : GeneratorTriangular b c g) :
    Function.Bijective (UniversalEnvelopingAlgebra.lift R g) := by
  have hT := canonicalCoordinates_bijective b c g hunit htri
  constructor
  · intro x y hxy
    apply (pbwBasis b).repr.injective
    apply hT.injective
    rw [canonicalCoordinates_repr, canonicalCoordinates_repr, hxy]
  · intro y
    obtain ⟨p, hp⟩ := hT.surjective (c.repr y)
    refine ⟨(pbwBasis b).repr.symm p, c.repr.injective ?_⟩
    exact hp

/-- The canonical algebra equivalence from the native enveloping algebra to
the given associative triangular target. -/
def canonicalEquiv (hunit : c 0 = 1) (htri : GeneratorTriangular b c g) :
    UniversalEnvelopingAlgebra R L ≃ₐ[R] B :=
  AlgEquiv.ofBijective (UniversalEnvelopingAlgebra.lift R g) (lift_bijective b c g hunit htri)

@[simp] theorem canonicalEquiv_apply (hunit : c 0 = 1) (htri : GeneratorTriangular b c g)
    (x : UniversalEnvelopingAlgebra R L) :
    canonicalEquiv b c g hunit htri x = UniversalEnvelopingAlgebra.lift R g x := rfl

@[simp] theorem canonicalEquiv_ι (hunit : c 0 = 1) (htri : GeneratorTriangular b c g) (x : L) :
    canonicalEquiv b c g hunit htri (ι R x) = g x :=
  UniversalEnvelopingAlgebra.lift_ι_apply R g x

@[simp] theorem canonicalEquiv_symm_generator (hunit : c 0 = 1)
    (htri : GeneratorTriangular b c g) (x : L) :
    (canonicalEquiv b c g hunit htri).symm (g x) = ι R x := by
  rw [← canonicalEquiv_ι b c g hunit htri x, AlgEquiv.symm_apply_apply]

/-- The equivalence preserves and reflects ordinary degree in the two bases. -/
theorem canonicalEquiv_filtered_iff (hunit : c 0 = 1) (htri : GeneratorTriangular b c g)
    (x : UniversalEnvelopingAlgebra R L) (n : ℕ) :
    c.repr (canonicalEquiv b c g hunit htri x) ∈
        Finsupp.supported R R {m | m.degree ≤ n} ↔
      (pbwBasis b).repr x ∈ Finsupp.supported R R {m | m.degree ≤ n} := by
  have h := triangular_mem_supported_iff Finsupp.degree (canonicalCoordinates b c g)
    (canonicalCoordinates_triangular b c g hunit htri) ((pbwBasis b).repr x) n
  rwa [canonicalCoordinates_repr] at h

/-- The inverse cannot increase polynomial degree. -/
theorem canonicalEquiv_symm_filtered (hunit : c 0 = 1) (htri : GeneratorTriangular b c g)
    {y : B} {n : ℕ} (hy : c.repr y ∈ Finsupp.supported R R {m | m.degree ≤ n}) :
    (pbwBasis b).repr ((canonicalEquiv b c g hunit htri).symm y) ∈
      Finsupp.supported R R {m | m.degree ≤ n} := by
  apply (canonicalEquiv_filtered_iff b c g hunit htri _ n).mp
  simpa only [AlgEquiv.apply_symm_apply] using hy

/-- The actual map is the identity on leading coordinates at every finite degree bound. -/
theorem canonicalEquiv_remainder_filtered (hunit : c 0 = 1)
    (htri : GeneratorTriangular b c g) {x : UniversalEnvelopingAlgebra R L} {n : ℕ}
    (hx : (pbwBasis b).repr x ∈ Finsupp.supported R R {m | m.degree ≤ n}) :
    c.repr (canonicalEquiv b c g hunit htri x) - (pbwBasis b).repr x ∈
      Finsupp.supported R R {m | m.degree < n} := by
  have h := triangular_remainder_mem_supported Finsupp.degree (canonicalCoordinates b c g)
    (canonicalCoordinates_triangular b c g hunit htri) hx
  rwa [canonicalCoordinates_repr] at h

/-- Any algebra equivalence with the prescribed generator values is this canonical map. -/
theorem canonicalEquiv_unique (hunit : c 0 = 1) (htri : GeneratorTriangular b c g)
    (e : UniversalEnvelopingAlgebra R L ≃ₐ[R] B) (he : ∀ x, e (ι R x) = g x) :
    e = canonicalEquiv b c g hunit htri := by
  have h : e.toAlgHom = (canonicalEquiv b c g hunit htri).toAlgHom := by
    apply EnvelopingIsomorphism.Enveloping.hom_ext_ι
    intro x
    exact (he x).trans (canonicalEquiv_ι b c g hunit htri x).symm
  ext x
  exact DFunLike.congr_fun h x

/-- Auxiliary ordered bases do not affect the canonical algebra equivalence. -/
theorem canonicalEquiv_basis_independent {β : Type*} [LinearOrder β]
    (b' : Module.Basis β R L) (c' : Module.Basis (β →₀ ℕ) R B)
    (hunit : c 0 = 1) (htri : GeneratorTriangular b c g)
    (hunit' : c' 0 = 1) (htri' : GeneratorTriangular b' c' g) :
    canonicalEquiv b c g hunit htri = canonicalEquiv b' c' g hunit' htri' := by
  ext x
  rfl

/-- Naturality follows from the original universal property: maps agreeing
on Lie generators agree on the entire enveloping algebra. -/
theorem canonicalEquiv_natural {M C : Type*} [LieRing M] [LieAlgebra R M]
    [Ring C] [Algebra R C] (g' : M →ₗ⁅R⁆ C) (f : L →ₗ⁅R⁆ M) (h : B →ₐ[R] C)
    (hunit : c 0 = 1) (htri : GeneratorTriangular b c g)
    (hgen : ∀ x, h (g x) = g' (f x)) :
    h.comp (canonicalEquiv b c g hunit htri).toAlgHom =
      (UniversalEnvelopingAlgebra.lift R g').comp (EnvelopingIsomorphism.Enveloping.map f) := by
  apply EnvelopingIsomorphism.Enveloping.hom_ext_ι
  intro x
  change h (canonicalEquiv b c g hunit htri (ι R x)) =
    UniversalEnvelopingAlgebra.lift R g' (EnvelopingIsomorphism.Enveloping.map f (ι R x))
  rw [canonicalEquiv_ι, EnvelopingIsomorphism.Enveloping.map_ι,
    UniversalEnvelopingAlgebra.lift_ι_apply]
  exact hgen x

end EnvelopingIsomorphism.PBW.FilteredTargetEquivalence
