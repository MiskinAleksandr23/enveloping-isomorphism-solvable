import EnvelopingIsomorphism.FormalSeries.Module
import Mathlib.LinearAlgebra.Multilinear.Curry

/-! Finite convolutions of multilinear maps on Laurent modules.

The index type of inputs is finite, but input and output modules may be
infinite-dimensional. A coefficient is summed over all exponent tuples whose
total is the output exponent. The support proof gives one common lower bound.
-/

noncomputable section

open scoped BigOperators
open Function

namespace EnvelopingIsomorphism.FormalSeries
namespace LaurentModule

variable {k ι : Type*} [CommRing k] [Fintype ι]
  {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)]
  {N P : Type*} [AddCommGroup N] [Module k N] [AddCommGroup P] [Module k P]

/-- Evaluation of a multilinear map at a fixed input tuple is linear in the map. -/
def evaluationLinear (v : ∀ i, M i) : MultilinearMap k M N →ₗ[k] N where
  toFun f := f v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype ι] in
@[simp] theorem evaluationLinear_apply (v : ∀ i, M i) (f : MultilinearMap k M N) :
    evaluationLinear v f = f v := rfl

/-- The integer tuples with a prescribed total and individual lower bounds form
a finite set. This is the coefficientwise finiteness behind Laurent convolution. -/
theorem finite_exponents (b : ι → ℤ) (d : ℤ) :
    {a : ι → ℤ | (∀ i, b i ≤ a i) ∧ ∑ i, a i = d}.Finite := by
  classical
  refine (Set.Finite.pi (fun i ↦ Set.finite_Icc (b i)
    (d - ∑ j ∈ Finset.univ.erase i, b j))).subset ?_
  intro a ha i hi
  refine ⟨ha.1 i, ?_⟩
  have hsum := Finset.sum_le_sum (s := Finset.univ.erase i) (fun j _ ↦ ha.1 j)
  have heq := Finset.sum_erase_add Finset.univ a (Finset.mem_univ i)
  have hatotal := ha.2
  omega

/-- The summand in a fixed Laurent coefficient. -/
def term (f : MultilinearMap k M N) (x : ∀ i, LaurentModule k (M i))
    (d : ℤ) (a : ι → ℤ) : N :=
  if ∑ i, a i = d then f (fun i ↦ coeff (x i) (a i)) else 0

theorem term_support (f : MultilinearMap k M N) (x : ∀ i, LaurentModule k (M i))
    {b : ι → ℤ} (hb : ∀ i, BoundedBelow (b i) (x i)) (d : ℤ) :
    Function.support (term f x d) ⊆
      {a : ι → ℤ | (∀ i, b i ≤ a i) ∧ ∑ i, a i = d} := by
  classical
  intro a ha
  have hn : term f x d a ≠ 0 := ha
  simp only [term, ne_eq, ite_eq_right_iff, Classical.not_imp] at hn
  refine ⟨?_, hn.1⟩
  intro i
  by_contra h
  exact hn.2 (f.map_coord_zero i (hb i _ (lt_of_not_ge h)))

theorem term_finite (f : MultilinearMap k M N) (x : ∀ i, LaurentModule k (M i)) (d : ℤ) :
    Function.HasFiniteSupport (term f x d) := by
  choose b hb using fun i ↦ exists_bound (x i)
  exact (finite_exponents b d).subset (term_support f x hb d)

/-- A coefficient of the multilinear Laurent extension, defined by a finite sum. -/
def convolutionCoeff (f : MultilinearMap k M N) (x : ∀ i, LaurentModule k (M i)) (d : ℤ) : N :=
  ∑ᶠ a : ι → ℤ, term f x d a

theorem convolutionCoeff_eq_sum (f : MultilinearMap k M N)
    (x : ∀ i, LaurentModule k (M i)) (d : ℤ) :
    convolutionCoeff f x d = ∑ a ∈ (term_finite f x d).toFinset, term f x d a := by
  exact finsum_eq_sum _ (term_finite f x d)

theorem convolutionCoeff_eq_zero_of_lt (f : MultilinearMap k M N)
    (x : ∀ i, LaurentModule k (M i)) {b : ι → ℤ}
    (hb : ∀ i, BoundedBelow (b i) (x i)) {d : ℤ} (hd : d < ∑ i, b i) :
    convolutionCoeff f x d = 0 := by
  apply finsum_eq_zero_of_forall_eq_zero
  intro a
  by_contra ha
  obtain ⟨ha, heq⟩ := term_support f x hb d ha
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ ha i)
  omega

/-- Apply a fixed finite-arity multilinear map to Laurent series by convolution. -/
def applyMultilinear (f : MultilinearMap k M N) (x : ∀ i, LaurentModule k (M i)) :
    LaurentModule k N :=
  HahnModule.of k (HahnSeries.ofSuppBddBelow (convolutionCoeff f x) (by
    choose b hb using fun i ↦ exists_bound (x i)
    refine ⟨∑ i, b i, ?_⟩
    intro d hd
    by_contra h
    exact hd (convolutionCoeff_eq_zero_of_lt f x hb (lt_of_not_ge h))))

@[simp] theorem coeff_applyMultilinear (f : MultilinearMap k M N)
    (x : ∀ i, LaurentModule k (M i)) (d : ℤ) :
    coeff (applyMultilinear f x) d = convolutionCoeff f x d := rfl

theorem boundedBelow_applyMultilinear (f : MultilinearMap k M N)
    (x : ∀ i, LaurentModule k (M i)) {b : ι → ℤ}
    (hb : ∀ i, BoundedBelow (b i) (x i)) :
    BoundedBelow (∑ i, b i) (applyMultilinear f x) :=
  fun _ hd ↦ convolutionCoeff_eq_zero_of_lt f x hb hd

omit [Fintype ι] in
private theorem coeff_update [DecidableEq ι] (x : ∀ i, LaurentModule k (M i))
    (i : ι) (y : LaurentModule k (M i)) (a : ι → ℤ) :
    (fun j ↦ coeff (Function.update x i y j) (a j)) =
      Function.update (fun j ↦ coeff (x j) (a j)) i (coeff y (a i)) := by
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [Function.update_of_ne h]

theorem term_update_add [DecidableEq ι] (f : MultilinearMap k M N)
    (x : ∀ i, LaurentModule k (M i)) (i : ι) (y z : LaurentModule k (M i))
    (d : ℤ) (a : ι → ℤ) :
    term f (Function.update x i (y + z)) d a =
      term f (Function.update x i y) d a + term f (Function.update x i z) d a := by
  simp only [term, coeff_update, coeff_add]
  split <;> simp_all [f.map_update_add]

theorem term_update_smul [DecidableEq ι] (f : MultilinearMap k M N)
    (x : ∀ i, LaurentModule k (M i)) (i : ι) (c : k) (y : LaurentModule k (M i))
    (d : ℤ) (a : ι → ℤ) :
    term f (Function.update x i (c • y)) d a =
      c • term f (Function.update x i y) d a := by
  simp only [term, coeff_update, coeff_smul]
  split <;> simp_all [f.map_update_smul]

/-- The extension is multilinear over the coefficient ring. -/
def extend (f : MultilinearMap k M N) :
    MultilinearMap k (fun i ↦ LaurentModule k (M i)) (LaurentModule k N) where
  toFun := applyMultilinear f
  map_update_add' x i y z := by
    ext d
    simp only [coeff_applyMultilinear, coeff_add, convolutionCoeff, term_update_add]
    exact finsum_add_distrib (term_finite f (Function.update x i y) d)
      (term_finite f (Function.update x i z) d)
  map_update_smul' x i c y := by
    ext d
    simp only [coeff_applyMultilinear, coeff_smul, convolutionCoeff, term_update_smul]
    exact (smul_finsum' c (term_finite f (Function.update x i y) d)).symm

@[simp] theorem extend_apply (f : MultilinearMap k M N)
    (x : ∀ i, LaurentModule k (M i)) : extend f x = applyMultilinear f x := rfl

/-- On monomials the extension adds exponents and applies the original map. -/
theorem applyMultilinear_single (f : MultilinearMap k M N) (b : ι → ℤ) (v : ∀ i, M i) :
    applyMultilinear f (fun i ↦ single (b i) (v i)) = single (∑ i, b i) (f v) := by
  classical
  ext d
  simp only [coeff_applyMultilinear, convolutionCoeff]
  rw [finsum_eq_single _ b]
  · simp [term, eq_comm]
  · intro a ha
    have hdiff : ∃ i, a i ≠ b i := by
      by_contra h
      push Not at h
      exact ha (funext h)
    obtain ⟨i, hi⟩ := hdiff
    simp only [term]
    split
    · exact f.map_coord_zero i (by simp [hi])
    · rfl

/-- Coefficientwise extension commutes with postcomposition by a linear map. -/
theorem applyMultilinear_postcomp (g : N →ₗ[k] P) (f : MultilinearMap k M N)
    (x : ∀ i, LaurentModule k (M i)) :
    applyMultilinear (g.compMultilinearMap f) x = map g (applyMultilinear f x) := by
  ext d
  simp only [coeff_applyMultilinear, coeff_map, convolutionCoeff]
  rw [map_finsum g (term_finite f x d)]
  apply finsum_congr
  intro a
  simp only [term]
  split <;> simp

/-- Coefficientwise extension commutes with a linear map on each input. -/
theorem applyMultilinear_precomp
    {M' : ι → Type*} [∀ i, AddCommGroup (M' i)] [∀ i, Module k (M' i)]
    (f : MultilinearMap k M' N) (g : ∀ i, M i →ₗ[k] M' i)
    (x : ∀ i, LaurentModule k (M i)) :
    applyMultilinear (f.compLinearMap g) x =
      applyMultilinear f (fun i ↦ map (g i) (x i)) := by
  ext d
  rfl

private def shiftCoordinate [DecidableEq ι] (i : ι) (e : ℤ) : (ι → ℤ) ≃ (ι → ℤ) where
  toFun a := Function.update a i (a i + e)
  invFun a := Function.update a i (a i - e)
  left_inv a := by
    funext j
    by_cases h : j = i <;> simp [h, Function.update_of_ne]
  right_inv a := by
    funext j
    by_cases h : j = i <;> simp [h, Function.update_of_ne]

private theorem sum_shiftCoordinate [DecidableEq ι] (i : ι) (e : ℤ) (a : ι → ℤ) :
    ∑ j, shiftCoordinate i e a j = (∑ j, a j) + e := by
  change (∑ j, Function.update a i (a i + e) j) = _
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  have h := Finset.sum_erase_add Finset.univ a (Finset.mem_univ i)
  rw [Finset.sdiff_singleton_eq_erase]
  omega

/-- Scalar monomials may be moved through any input of the convolution. -/
theorem applyMultilinear_update_single_smul [DecidableEq ι]
    (f : MultilinearMap k M N) (x : ∀ i, LaurentModule k (M i))
    (i : ι) (e : ℤ) (c : k) (y : LaurentModule k (M i)) :
    applyMultilinear f (Function.update x i (HahnSeries.single e c • y)) =
      HahnSeries.single e c • applyMultilinear f (Function.update x i y) := by
  classical
  ext d
  simp only [coeff_applyMultilinear, coeff_series_single_smul, convolutionCoeff]
  rw [smul_finsum' c (term_finite f (Function.update x i y) (d - e))]
  calc
    (∑ᶠ a, term f (Function.update x i (HahnSeries.single e c • y)) d a) =
        ∑ᶠ a, term f (Function.update x i (HahnSeries.single e c • y)) d
          (shiftCoordinate i e a) := (finsum_comp_equiv (shiftCoordinate i e)).symm
    _ = _ := by
      apply finsum_congr
      intro a
      have hcoeff :
          (fun j ↦ coeff (Function.update x i (HahnSeries.single e c • y) j)
            (shiftCoordinate i e a j)) =
          Function.update (fun j ↦ coeff (Function.update x i y j) (a j))
            i (c • coeff y (a i)) := by
        funext j
        by_cases h : j = i
        · subst j; simp [shiftCoordinate]
        · simp [shiftCoordinate, h]
      have heval :
          f (fun j ↦ coeff (Function.update x i (HahnSeries.single e c • y) j)
            (shiftCoordinate i e a j)) =
          c • f (fun j ↦ coeff (Function.update x i y j) (a j)) := by
        rw [hcoeff, f.map_update_smul]
        congr 1
        congr 1
        funext j
        by_cases h : j = i
        · subst j; simp
        · simp [Function.update_of_ne h]
      simp only [term, sum_shiftCoordinate, heval]
      by_cases h : ∑ j, a j = d - e
      · simp [h]
      · have h' : (∑ j, a j) + e ≠ d := by omega
        simp [h, h']

/-- The finite convolution is multilinear over the full Laurent scalar ring. -/
theorem applyMultilinear_update_series_smul [DecidableEq ι]
    (f : MultilinearMap k M N) (x : ∀ i, LaurentModule k (M i))
    (i : ι) (a : LaurentSeries k) (y : LaurentModule k (M i)) :
    applyMultilinear f (Function.update x i (a • y)) =
      a • applyMultilinear f (Function.update x i y) := by
  classical
  choose b hb using fun j ↦ exists_bound (x j)
  apply map_series_smul_of_bounded ((extend f).toLinearMap x i)
    (∑ j ∈ Finset.univ.erase i, b j)
  · intro B z hz
    have h := boundedBelow_applyMultilinear f (Function.update x i z)
      (b := Function.update b i B) (by
        intro j
        by_cases hij : j = i
        · subst j; simpa using hz
        · simpa [Function.update_of_ne hij] using hb j)
    simpa [Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase] using h
  · intro e c z
    exact applyMultilinear_update_single_smul f x i e c z

/-- The Laurent-linear extension of an arbitrary finite-arity multilinear map. -/
def extendScalars (f : MultilinearMap k M N) :
    MultilinearMap (LaurentSeries k) (fun i ↦ LaurentModule k (M i)) (LaurentModule k N) where
  toFun := applyMultilinear f
  map_update_add' x i y z := (extend f).map_update_add x i y z
  map_update_smul' x i a y := applyMultilinear_update_series_smul f x i a y

@[simp] theorem extendScalars_apply (f : MultilinearMap k M N)
    (x : ∀ i, LaurentModule k (M i)) : extendScalars f x = applyMultilinear f x := rfl

/-- Bounded multilinear operations are determined by their values on tuples of monomials. -/
theorem multilinear_eq_zero_of_bounded
    (F : MultilinearMap k (fun i ↦ LaurentModule k (M i)) (LaurentModule k N))
    (C : ℤ)
    (hbound : ∀ (x : ∀ i, LaurentModule k (M i)) (b : ι → ℤ), (∀ i, BoundedBelow (b i) (x i)) →
      BoundedBelow ((∑ i, b i) + C) (F x))
    (hsingle : ∀ (b : ι → ℤ) (v : ∀ i, M i), F (fun i ↦ single (b i) (v i)) = 0) : F = 0 := by
  classical
  have hfinite : ∀ s : Finset ι, ∀ x : ∀ i, LaurentModule k (M i),
      (∀ i ∉ s, ∃ e v, x i = single e v) → F x = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro x hx
        choose b v hv using fun i ↦ hx i (Finset.notMem_empty i)
        have heq : x = fun i ↦ single (b i) (v i) := funext hv
        rw [heq]
        exact hsingle b v
    | @insert i s his ih =>
        intro x hx
        choose b hb using fun j ↦ exists_bound (x j)
        have hz : F.toLinearMap x i = 0 := by
          apply linear_eq_zero_of_bounded (F.toLinearMap x i)
            ((∑ j ∈ Finset.univ.erase i, b j) + C)
          · intro B z hz
            have h := hbound (Function.update x i z) (Function.update b i B) (by
              intro j
              by_cases hji : j = i
              · subst j; simpa using hz
              · simpa [Function.update_of_ne hji] using hb j)
            simpa [Finset.sum_update_of_mem (Finset.mem_univ i),
              Finset.sdiff_singleton_eq_erase, add_assoc] using h
          · intro e v
            apply ih (Function.update x i (single e v))
            intro j hj
            by_cases hji : j = i
            · subst j; exact ⟨e, v, by simp⟩
            · obtain ⟨ej, vj, hvj⟩ := hx j (by simp [hj, hji])
              exact ⟨ej, vj, by simpa [Function.update_of_ne hji] using hvj⟩
        have h := DFunLike.congr_fun hz (x i)
        simpa using h
  apply MultilinearMap.ext
  intro x
  exact hfinite Finset.univ x (by simp)

/-- Equality of uniformly bounded multilinear operations can be checked on monomials. -/
theorem multilinear_ext_of_bounded
    (F G : MultilinearMap k (fun i ↦ LaurentModule k (M i)) (LaurentModule k N))
    (C : ℤ)
    (hF : ∀ (x : ∀ i, LaurentModule k (M i)) (b : ι → ℤ), (∀ i, BoundedBelow (b i) (x i)) →
      BoundedBelow ((∑ i, b i) + C) (F x))
    (hG : ∀ (x : ∀ i, LaurentModule k (M i)) (b : ι → ℤ), (∀ i, BoundedBelow (b i) (x i)) →
      BoundedBelow ((∑ i, b i) + C) (G x))
    (hsingle : ∀ (b : ι → ℤ) (v : ∀ i, M i), F (fun i ↦ single (b i) (v i)) =
      G (fun i ↦ single (b i) (v i))) : F = G := by
  apply sub_eq_zero.mp
  apply multilinear_eq_zero_of_bounded (F - G) C
  · intro x b hb d hd
    change coeff (F x - G x) d = 0
    simp only [coeff_sub, hF x b hb d hd, hG x b hb d hd, sub_self]
  · intro b v
    change F (fun i ↦ single (b i) (v i)) - G (fun i ↦ single (b i) (v i)) = 0
    exact sub_eq_zero.mpr (hsingle b v)

/-- Extension commutes with arbitrary finite-arity substitution of multilinear maps.
This proves the required interchange of the finite coefficient convolutions without
assuming finite-dimensionality of any coefficient module. -/
theorem extend_compMultilinearMap
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    {V : (i : ι) → κ i → Type*} [∀ i j, AddCommGroup (V i j)] [∀ i j, Module k (V i j)]
    (f : MultilinearMap k M N) (g : ∀ i, MultilinearMap k (V i) (M i)) :
    extend (f.compMultilinearMap g) =
      (extend f).compMultilinearMap (fun i ↦ extend (g i)) := by
  apply multilinear_ext_of_bounded _ _ 0
  · intro x b hb
    simpa only [add_zero, extend_apply] using
      boundedBelow_applyMultilinear (f.compMultilinearMap g) x hb
  · intro x b hb
    change BoundedBelow ((∑ j, b j) + 0)
      (applyMultilinear f (fun i ↦ applyMultilinear (g i) (fun j ↦ x ⟨i, j⟩)))
    have h := boundedBelow_applyMultilinear f
      (fun i ↦ applyMultilinear (g i) (fun j ↦ x ⟨i, j⟩))
      (b := fun i ↦ ∑ j, b ⟨i, j⟩) (fun i ↦
        boundedBelow_applyMultilinear (g i) (fun j ↦ x ⟨i, j⟩)
          (b := fun j ↦ b ⟨i, j⟩) (fun j ↦ hb ⟨i, j⟩))
    simpa only [add_zero, Fintype.sum_sigma] using h
  · intro b v
    change applyMultilinear (f.compMultilinearMap g) (fun j ↦ single (b j) (v j)) =
      applyMultilinear f (fun i ↦ applyMultilinear (g i)
        (fun j ↦ single (b ⟨i, j⟩) (v ⟨i, j⟩)))
    simp_rw [applyMultilinear_single]
    simp only [MultilinearMap.compMultilinearMap_apply, Fintype.sum_sigma]
    rfl

/-- Laurent-scalar version of compatibility with substitution. -/
theorem extendScalars_compMultilinearMap
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    {V : (i : ι) → κ i → Type*} [∀ i j, AddCommGroup (V i j)] [∀ i j, Module k (V i j)]
    (f : MultilinearMap k M N) (g : ∀ i, MultilinearMap k (V i) (M i)) :
    extendScalars (f.compMultilinearMap g) =
      (extendScalars f).compMultilinearMap (fun i ↦ extendScalars (g i)) := by
  apply MultilinearMap.ext
  intro x
  exact DFunLike.congr_fun (extend_compMultilinearMap f g) x

section Cochains

universe u
variable {X Y : Type u} [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]

/-- Polynomial Hochschild-type cochains of arity n, before any completion.
The definition also includes arity zero. -/
abbrev Cochain (k X Y : Type*) [CommRing k] [AddCommGroup X] [Module k X]
    [AddCommGroup Y] [Module k Y] (n : ℕ) :=
  MultilinearMap k (fun _ : Fin n ↦ X) Y

abbrev CochainInput (n : ℕ) : Fin (n + 1) → Type u :=
  Fin.cases (Cochain k X Y n) (fun _ : Fin n ↦ X)

instance cochainInputAddCommGroup (n : ℕ) (i : Fin (n + 1)) :
    AddCommGroup (CochainInput (k := k) (X := X) (Y := Y) n i) := by
  cases i using Fin.cases
  · change AddCommGroup (Cochain k X Y n)
    infer_instance
  · change AddCommGroup X
    infer_instance

instance cochainInputModule (n : ℕ) (i : Fin (n + 1)) :
    Module k (CochainInput (k := k) (X := X) (Y := Y) n i) := by
  cases i using Fin.cases
  · change Module k (Cochain k X Y n)
    infer_instance
  · change Module k X
    infer_instance

/-- The evaluation operation is multilinear in the cochain and its inputs. -/
def cochainEvaluation (n : ℕ) :
    MultilinearMap k (CochainInput (k := k) (X := X) (Y := Y) n) Y :=
  LinearMap.uncurryLeft (LinearMap.id : Cochain k X Y n →ₗ[k] Cochain k X Y n)

/-- A Laurent series of cochains acts on Laurent inputs by simultaneous
convolution. This is a map into, not an identification with, all multilinear
maps over the Laurent scalar ring. -/
def extendCochain (n : ℕ) :
    LaurentModule k (Cochain k X Y n) →ₗ[LaurentSeries k]
      MultilinearMap (LaurentSeries k) (fun _ : Fin n ↦ LaurentModule k X)
        (LaurentModule k Y) :=
  (extendScalars (cochainEvaluation (k := k) (X := X) (Y := Y) n)).curryLeft

theorem extendCochain_apply (n : ℕ) (F : LaurentModule k (Cochain k X Y n))
    (x : Fin n → LaurentModule k X) :
    extendCochain n F x = applyMultilinear
      (cochainEvaluation (k := k) (X := X) (Y := Y) n) (Fin.cons F x) := rfl

@[simp] theorem coeff_extendCochain (n : ℕ) (F : LaurentModule k (Cochain k X Y n))
    (x : Fin n → LaurentModule k X) (d : ℤ) :
    coeff (extendCochain n F x) d =
      ∑ᶠ a : Fin (n + 1) → ℤ,
        if ∑ i, a i = d then (coeff F (a 0)) (fun i ↦ coeff (x i) (a i.succ)) else 0 := rfl

/-- One cochain lower bound and the input lower bounds give a single output bound. -/
theorem boundedBelow_extendCochain (n : ℕ) (F : LaurentModule k (Cochain k X Y n))
    (x : Fin n → LaurentModule k X) {B : ℤ} {b : Fin n → ℤ}
    (hF : BoundedBelow B F) (hx : ∀ i, BoundedBelow (b i) (x i)) :
    BoundedBelow (B + ∑ i, b i) (extendCochain n F x) := by
  rw [extendCochain_apply]
  have h := boundedBelow_applyMultilinear (cochainEvaluation (k := k) (X := X) (Y := Y) n)
    (Fin.cons F x) (b := Fin.cons B b) (by
      intro i
      cases i using Fin.cases
      · exact hF
      · exact hx _)
  simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] using h

/-- The coefficient sum in cochain evaluation is actually finite, uniformly over
the possibly infinite-dimensional coefficient modules. -/
theorem finite_support_extendCochain (n : ℕ) (F : LaurentModule k (Cochain k X Y n))
    (x : Fin n → LaurentModule k X) (d : ℤ) :
    Function.HasFiniteSupport (fun a : Fin (n + 1) → ℤ ↦
      if ∑ i, a i = d then (coeff F (a 0)) (fun i ↦ coeff (x i) (a i.succ)) else 0) :=
  term_finite (cochainEvaluation (k := k) (X := X) (Y := Y) n) (Fin.cons F x) d

/-- Simultaneous monomial inputs recover the original evaluation. -/
theorem extendCochain_single (n : ℕ) (f : Cochain k X Y n) (e : ℤ)
    (b : Fin n → ℤ) (v : Fin n → X) :
    extendCochain n (single e f) (fun i ↦ single (b i) (v i)) =
      single (e + ∑ i, b i) (f v) := by
  rw [extendCochain_apply]
  have h := applyMultilinear_single (cochainEvaluation (k := k) (X := X) (Y := Y) n)
    (Fin.cons e b) (Fin.cons f v)
  have harg :
      (fun i : Fin (n + 1) ↦ single (k := k) ((Fin.cons e b : Fin (n + 1) → ℤ) i)
        ((Fin.cons f v : ∀ i, CochainInput (k := k) (X := X) (Y := Y) n i) i)) =
      (Fin.cons (single e f) (fun i ↦ single (k := k) (b i) (v i)) :
        ∀ i, LaurentModule k (CochainInput (k := k) (X := X) (Y := Y) n i)) := by
    funext i
    cases i using Fin.cases <;> rfl
  rw [harg] at h
  have hval : cochainEvaluation (k := k) (X := X) (Y := Y) n (Fin.cons f v) = f v := rfl
  rw [hval] at h
  convert h using 1
  · rfl
  · congr 1
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-- A constant cochain series acts by the ordinary Laurent extension of that cochain. -/
theorem extendCochain_single_zero (n : ℕ) (f : Cochain k X Y n) :
    extendCochain n (single 0 f) = extendScalars f := by
  have h : (extendCochain n (single 0 f)).restrictScalars k = extend f := by
    apply multilinear_ext_of_bounded _ _ 0
    · intro x b hb
      change BoundedBelow ((∑ i, b i) + 0) (extendCochain n (single 0 f) x)
      simpa only [zero_add, add_zero] using boundedBelow_extendCochain n (single 0 f) x
        (boundedBelow_single 0 f) hb
    · intro x b hb
      simpa only [add_zero, extend_apply] using boundedBelow_applyMultilinear f x hb
    · intro b v
      change extendCochain n (single 0 f) (fun i ↦ single (b i) (v i)) =
        applyMultilinear f (fun i ↦ single (b i) (v i))
      rw [extendCochain_single, applyMultilinear_single, zero_add]
  apply MultilinearMap.ext
  intro x
  exact DFunLike.congr_fun h x

/-- Linear postcomposition of Laurent cochains commutes with evaluation on Laurent inputs. -/
theorem extendCochain_postcomp {Z : Type u} [AddCommGroup Z] [Module k Z]
    (n : ℕ) (g : Y →ₗ[k] Z) (F : LaurentModule k (Cochain k X Y n))
    (x : Fin n → LaurentModule k X) :
    extendCochain n (map (g.compMultilinearMapₗ k) F) x = map g (extendCochain n F x) := by
  ext d
  simp only [coeff_extendCochain, coeff_map]
  rw [map_finsum g (finite_support_extendCochain n F x d)]
  apply finsum_congr
  intro a
  split <;> simp

/-- A fixed linear substitution on the arguments commutes with Laurent cochain evaluation. -/
theorem extendCochain_precomp {X' : Type u} [AddCommGroup X'] [Module k X']
    (n : ℕ) (g : X' →ₗ[k] X) (F : LaurentModule k (Cochain k X Y n))
    (x : Fin n → LaurentModule k X') :
    extendCochain n (map (MultilinearMap.compLinearMapₗ (fun _ : Fin n ↦ g)) F) x =
      extendCochain n F (fun i ↦ map g (x i)) := by
  ext d
  rfl

/-- On constant argument series, a Laurent cochain is evaluated coefficientwise. -/
theorem extendCochain_constants (n : ℕ) (F : LaurentModule k (Cochain k X Y n))
    (v : Fin n → X) :
    extendCochain n F (fun i ↦ single 0 (v i)) = map (evaluationLinear v) F := by
  let T : LaurentModule k (Cochain k X Y n) →ₗ[LaurentSeries k] LaurentModule k Y :=
    (evaluationLinear (k := LaurentSeries k) (fun i ↦ single (k := k) 0 (v i))).comp
      (extendCochain n)
  let S := map (evaluationLinear (k := k) (N := Y) v)
  have heq : T.restrictScalars k = S.restrictScalars k := by
    apply linear_ext_of_bounded _ _ 0
    · intro B G hG
      change BoundedBelow (B + 0) (extendCochain n G (fun i ↦ single 0 (v i)))
      simpa only [Finset.sum_const_zero] using boundedBelow_extendCochain n G
        (fun i ↦ single 0 (v i)) (b := fun _ ↦ 0) hG (fun i ↦ boundedBelow_single 0 (v i))
    · intro B G hG
      change BoundedBelow (B + 0) (map (evaluationLinear v) G)
      simpa only [add_zero] using boundedBelow_map (evaluationLinear v) hG
    · intro e f
      change extendCochain n (single e f) (fun i ↦ single 0 (v i)) =
        map (evaluationLinear v) (single e f)
      rw [extendCochain_single, map_single]
      simp
  exact DFunLike.congr_fun heq F

/-- The cochain series representation is faithful; it is not enlarged to all
Laurent-linear multilinear maps. -/
theorem extendCochain_injective (n : ℕ) :
    Function.Injective (extendCochain (k := k) (X := X) (Y := Y) n) := by
  intro F G h
  apply LaurentModule.ext
  intro d
  apply MultilinearMap.ext
  intro v
  have hv := congrArg (fun H : MultilinearMap (LaurentSeries k)
      (fun _ : Fin n ↦ LaurentModule k X) (LaurentModule k Y) ↦
        coeff (H (fun i ↦ single 0 (v i))) d) h
  simpa only [extendCochain_constants, coeff_map, evaluationLinear_apply] using hv

end Cochains

/-! `extendScalars` also preserves the linear operations on the space of fixed
cochains. This lets finite identities between multilinear operations pass to
the Laurent modules term by term. -/

theorem extendScalars_add (f g : MultilinearMap k M N) :
    extendScalars (f + g) = extendScalars f + extendScalars g := by
  apply MultilinearMap.ext
  intro x
  ext d
  change convolutionCoeff (f + g) x d = convolutionCoeff f x d + convolutionCoeff g x d
  simp only [convolutionCoeff]
  rw [← finsum_add_distrib (term_finite f x d) (term_finite g x d)]
  apply finsum_congr
  intro a
  simp only [term]
  split <;> simp

theorem extendScalars_smul (c : k) (f : MultilinearMap k M N) :
    extendScalars (c • f) = (HahnSeries.single (0 : ℤ) c : LaurentSeries k) • extendScalars f := by
  apply MultilinearMap.ext
  intro x
  ext d
  change convolutionCoeff (c • f) x d = coeff (HahnSeries.single (0 : ℤ) c • applyMultilinear f x) d
  rw [coeff_series_single_smul, sub_zero, coeff_applyMultilinear]
  simp only [convolutionCoeff]
  rw [smul_finsum' c (term_finite f x d)]
  apply finsum_congr
  intro a
  simp only [term]
  split <;> simp

theorem extendScalars_zero : extendScalars (0 : MultilinearMap k M N) = 0 := by
  apply MultilinearMap.ext
  intro x
  ext d
  change convolutionCoeff 0 x d = 0
  simp [convolutionCoeff, term]

end LaurentModule
end EnvelopingIsomorphism.FormalSeries
