import EnvelopingIsomorphism.PBW.Basis
import EnvelopingIsomorphism.PBW.Leading
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.Ring.GeomSum

/-! The actual averaging map used in PBW symmetrization. -/

noncomputable section

namespace EnvelopingIsomorphism.PBW

open scoped BigOperators

attribute [local instance 100] LieRing.ofAssociativeRing

section Averaging

variable (R : Type*) [CommRing R] [Algebra ℚ R]
variable (A : Type*) [Ring A] [Algebra R A]

/-- The inverse factorial as a scalar of the coefficient algebra. -/
def inverseFactorial (n : ℕ) : R := algebraMap ℚ R ((n.factorial : ℚ)⁻¹)

theorem inverseFactorial_mul_factorial (n : ℕ) :
    inverseFactorial R n * (n.factorial : R) = 1 := by
  have h : (n.factorial : ℚ)⁻¹ * (n.factorial : ℚ) = 1 :=
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  simpa only [inverseFactorial, map_mul, map_natCast, map_one] using
    congrArg (algebraMap ℚ R) h

/-- Average all orders of an ordered product, as an actual multilinear map. -/
def averagedProduct (n : ℕ) : MultilinearMap R (fun _ : Fin n ↦ A) A :=
  inverseFactorial R n •
    ∑ σ : Equiv.Perm (Fin n), (MultilinearMap.mkPiAlgebraFin R n A).domDomCongr σ

theorem averagedProduct_apply (n : ℕ) (v : Fin n → A) :
    averagedProduct R A n v = inverseFactorial R n •
      ∑ σ : Equiv.Perm (Fin n), (List.ofFn (v ∘ σ)).prod := by
  simp [averagedProduct, MultilinearMap.domDomCongr_apply,
    MultilinearMap.mkPiAlgebraFin_apply, Function.comp_def]

theorem averagedProduct_perm (n : ℕ) (τ : Equiv.Perm (Fin n)) (v : Fin n → A) :
    averagedProduct R A n (v ∘ τ) = averagedProduct R A n v := by
  rw [averagedProduct_apply, averagedProduct_apply]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ ↦ rfl)

theorem averagedProduct_reindex {n m : ℕ} (e : Fin n ≃ Fin m) (v : Fin m → A) :
    averagedProduct R A n (v ∘ e) = averagedProduct R A m v := by
  have h : n = m := by simpa using Fintype.card_congr e
  subst m
  exact averagedProduct_perm R A n e v

/-- Symmetric averaging applied to a list of associative-algebra elements. -/
def averagedWord (w : List A) : A := averagedProduct R A w.length w.get

private theorem perm_index_equiv {B : Type*} {xs ys : List B} (h : xs.Perm ys) :
    ∃ e : Fin xs.length ≃ Fin ys.length, ∀ i, xs.get i = ys.get (e i) := by
  induction h with
  | nil => exact ⟨Equiv.refl _, fun i ↦ Fin.elim0 i⟩
  | cons x h ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨((finSuccEquiv _).trans (Equiv.optionCongr e)).trans (finSuccEquiv _).symm, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp
    · simpa using he j
  | swap x y zs =>
    refine ⟨Equiv.swap 0 1, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ ?_) j) i
    · simp
    · simp
    · have h0 : k.succ.succ ≠ (0 : Fin (zs.length + 2)) := Fin.succ_ne_zero _
      have h1 : k.succ.succ ≠ (1 : Fin (zs.length + 2)) := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_succ, Fin.val_one] at hv
        omega
      simp [Equiv.swap_apply_of_ne_of_ne h0 h1]
  | trans h₁ h₂ ih₁ ih₂ =>
    obtain ⟨e, he⟩ := ih₁
    obtain ⟨f, hf⟩ := ih₂
    exact ⟨e.trans f, fun i ↦ (he i).trans (hf (e i))⟩

theorem averagedWord_perm {xs ys : List A} (h : xs.Perm ys) :
    averagedWord R A xs = averagedWord R A ys := by
  obtain ⟨e, he⟩ := perm_index_equiv h
  unfold averagedWord
  rw [show xs.get = ys.get ∘ e from funext he]
  exact averagedProduct_reindex R A e ys.get

theorem averagedWord_ofFn {n : ℕ} (v : Fin n → A) :
    averagedWord R A (List.ofFn v) = averagedProduct R A n v := by
  let e : Fin (List.ofFn v).length ≃ Fin n := finCongr List.length_ofFn
  have he : (List.ofFn v).get = v ∘ e := by
    funext i
    simp only [List.get_eq_getElem, List.getElem_ofFn, Function.comp_apply]
    congr 1
  unfold averagedWord
  rw [he]
  exact averagedProduct_reindex R A e v

theorem averagedWord_map {B : Type*} (f : B → A) (w : List B) :
    averagedWord R A (w.map f) = averagedProduct R A w.length (f ∘ w.get) := by
  have h : w.map f = List.ofFn (f ∘ w.get) := by
    rw [← List.map_ofFn, List.ofFn_get]
  rw [h, averagedWord_ofFn]

theorem inverseFactorial_smul_sum_const {V : Type*} [AddCommMonoid V] [Module R V]
    (n : ℕ) (x : V) :
    inverseFactorial R n • (∑ _ : Equiv.Perm (Fin n), x) = x := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul R, smul_smul, inverseFactorial_mul_factorial, one_smul]

@[simp] theorem averagedProduct_const (n : ℕ) (a : A) :
    averagedProduct R A n (fun _ ↦ a) = a ^ n := by
  rw [averagedProduct_apply]
  simp only [Function.comp_def, List.ofFn_const, List.prod_replicate]
  exact inverseFactorial_smul_sum_const R n (a ^ n)

end Averaging

section SymmetricAlgebraMap

variable {R L α : Type*} [CommRing R] [Algebra ℚ R]
variable [LieRing L] [LieAlgebra R L] [LinearOrder α]
variable (b : Module.Basis α R L)

omit [Algebra ℚ R] in
theorem symmetricAlgebra_basis_wordIndex (w : List α) :
    b.symmetricAlgebra (wordIndex w) =
      (w.map (SymmetricAlgebra.ι R L ∘ b)).prod := by
  apply (SymmetricAlgebra.equivMvPolynomial b).injective
  simp only [Module.Basis.symmetricAlgebra, Module.Basis.map_apply,
    AlgEquiv.toLinearEquiv_apply, AlgEquiv.apply_symm_apply]
  change MvPolynomial.monomial (wordIndex w) 1 = _
  induction w with
  | nil => simp
  | cons i w ih =>
    simp only [wordIndex_cons, List.map_cons, List.prod_cons, map_mul, Function.comp_apply,
      SymmetricAlgebra.equivMvPolynomial_ι_apply, ← ih]
    rw [add_comm, MvPolynomial.monomial_add_single, pow_one, mul_comm]

/-- The PBW symmetrization map is the actual permutation average on commutative monomials. -/
def symmetrization : SymmetricAlgebra R L →ₗ[R] UniversalEnvelopingAlgebra R L :=
  b.symmetricAlgebra.constr R fun m ↦
    averagedWord R (UniversalEnvelopingAlgebra R L)
      ((orderedWord m).map (UniversalEnvelopingAlgebra.ι R ∘ b))

@[simp] theorem symmetrization_basis (m : α →₀ ℕ) :
    symmetrization b (b.symmetricAlgebra m) =
      averagedWord R (UniversalEnvelopingAlgebra R L)
        ((orderedWord m).map (UniversalEnvelopingAlgebra.ι R ∘ b)) := by
  simp [symmetrization]

theorem symmetrization_basis_word (w : List α) :
    symmetrization b ((w.map (SymmetricAlgebra.ι R L ∘ b)).prod) =
      averagedWord R (UniversalEnvelopingAlgebra R L)
        (w.map (UniversalEnvelopingAlgebra.ι R ∘ b)) := by
  rw [← symmetricAlgebra_basis_wordIndex, symmetrization_basis]
  apply averagedWord_perm
  apply List.Perm.map
  exact wordIndex_eq_iff_perm.mp (wordIndex_orderedWord (wordIndex w))

/-- Symmetrization averages products of arbitrary Lie vectors, not only basis vectors. -/
theorem symmetrization_prod (n : ℕ) (v : Fin n → L) :
    symmetrization b ((List.ofFn (fun i ↦ SymmetricAlgebra.ι R L (v i))).prod) =
      averagedProduct R (UniversalEnvelopingAlgebra R L) n
        (fun i ↦ UniversalEnvelopingAlgebra.ι R (v i)) := by
  let p : MultilinearMap R (fun _ : Fin n ↦ L) (SymmetricAlgebra R L) :=
    (MultilinearMap.mkPiAlgebraFin R n (SymmetricAlgebra R L)).compLinearMap
      (fun _ ↦ SymmetricAlgebra.ι R L)
  let q : MultilinearMap R (fun _ : Fin n ↦ L) (UniversalEnvelopingAlgebra R L) :=
    (averagedProduct R (UniversalEnvelopingAlgebra R L) n).compLinearMap
      (fun _ ↦ (UniversalEnvelopingAlgebra.ι R).toLinearMap)
  have h : (symmetrization b).compMultilinearMap p = q := by
    apply Module.Basis.ext_multilinear (fun _ : Fin n ↦ b)
    intro a
    change symmetrization b
      ((List.ofFn (fun i ↦ SymmetricAlgebra.ι R L (b (a i)))).prod) =
      averagedProduct R (UniversalEnvelopingAlgebra R L) n
        (fun i ↦ UniversalEnvelopingAlgebra.ι R (b (a i)))
    simpa only [List.map_ofFn, Function.comp_def, averagedWord_ofFn] using
      symmetrization_basis_word b (List.ofFn a)
  exact MultilinearMap.congr_fun h v

@[simp] theorem symmetrization_one : symmetrization b 1 = 1 := by
  simpa using symmetrization_prod b 0 (fun _ ↦ (0 : L))

@[simp] theorem symmetrization_ι (x : L) :
    symmetrization b (SymmetricAlgebra.ι R L x) = UniversalEnvelopingAlgebra.ι R x := by
  simpa using symmetrization_prod b 1 (fun _ ↦ x)

/-- The averaging map is independent of the ordered basis used to construct it. -/
theorem symmetrization_basis_independent {β : Type*} [LinearOrder β]
    (c : Module.Basis β R L) : symmetrization b = symmetrization c := by
  apply b.symmetricAlgebra.ext
  intro m
  have hm := symmetricAlgebra_basis_wordIndex b (orderedWord m)
  rw [wordIndex_orderedWord] at hm
  rw [hm]
  have hw : (orderedWord m).map (SymmetricAlgebra.ι R L ∘ b) =
      List.ofFn (fun i ↦ SymmetricAlgebra.ι R L (b ((orderedWord m).get i))) := by
    change _ = List.ofFn ((SymmetricAlgebra.ι R L ∘ b) ∘ (orderedWord m).get)
    rw [← List.map_ofFn, List.ofFn_get]
  rw [hw, symmetrization_prod, symmetrization_prod]

end SymmetricAlgebraMap

section TriangularInverse

variable {R β : Type*} [CommRing R]

/-- A strictly degree-lowering endomorphism is nilpotent on each finite-support input. -/
theorem locallyNilpotent_of_degree_lowering (d : β → ℕ)
    (D : Module.End R (β →₀ R))
    (hD : ∀ i, D (Finsupp.single i 1) ∈
      Finsupp.supported R R {j | d j < d i}) :
    ∀ p, ∃ n, (D ^ n) p = 0 := by
  classical
  have step (n : ℕ) {p : β →₀ R}
      (hp : p ∈ Finsupp.supported R R {i | d i < n + 1}) :
      D p ∈ Finsupp.supported R R {i | d i < n} := by
    rw [Finsupp.supported_eq_span_single] at hp
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      apply Finsupp.supported_mono (M := R) (R := R) _ (hD i)
      intro j hj
      change d j < d i at hj
      change d i < n + 1 at hi
      change d j < n
      omega
    | zero => simp
    | add x y _ _ hx hy => simpa only [map_add] using add_mem hx hy
    | smul r x _ hx => simpa only [map_smul] using Submodule.smul_mem _ r hx
  have nil (n : ℕ) : ∀ p : β →₀ R,
      p ∈ Finsupp.supported R R {i | d i < n} → (D ^ n) p = 0 := by
    induction n with
    | zero =>
      intro p hp
      have hp0 : p = 0 := by
        ext i
        exact (Finsupp.mem_supported' R p).mp hp i (by simp)
      simp [hp0]
    | succ n ih =>
      intro p hp
      simpa only [pow_succ, Module.End.mul_apply] using ih (D p) (step n hp)
  intro p
  refine ⟨p.support.sup d + 1, nil _ p ?_⟩
  intro i hi
  exact lt_of_le_of_lt (Finset.le_sup hi) (Nat.lt_succ_self _)

/-- A finite geometric sum gives an inverse on each input of `1 - D`. -/
theorem bijective_one_sub_of_locallyNilpotent {V : Type*} [AddCommGroup V] [Module R V]
    (D : Module.End R V) (hD : ∀ x, ∃ n, (D ^ n) x = 0) :
    Function.Bijective (1 - D : Module.End R V) := by
  constructor
  · intro x y hxy
    have hzero : (1 - D : Module.End R V) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hfix : D (x - y) = x - y := by
      change x - y - D (x - y) = 0 at hzero
      exact (sub_eq_zero.mp hzero).symm
    have hp (n : ℕ) : (D ^ n) (x - y) = x - y := by
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, Module.End.mul_apply, hfix, ih]
    obtain ⟨n, hn⟩ := hD (x - y)
    exact sub_eq_zero.mp ((hp n).symm.trans hn)
  · intro x
    obtain ⟨n, hn⟩ := hD x
    refine ⟨(∑ i ∈ Finset.range n, D ^ i) x, ?_⟩
    change ((1 - D) * ∑ i ∈ Finset.range n, D ^ i) x = x
    rw [mul_neg_geom_sum]
    simp only [LinearMap.sub_apply, Module.End.one_apply, hn, sub_zero]

/-- A map which is the identity modulo lower-degree terms is a linear isomorphism. -/
theorem bijective_of_degree_triangular (d : β → ℕ)
    (T : Module.End R (β →₀ R))
    (hT : ∀ i, T (Finsupp.single i 1) - Finsupp.single i 1 ∈
      Finsupp.supported R R {j | d j < d i}) : Function.Bijective T := by
  let D : Module.End R (β →₀ R) := 1 - T
  have hD : ∀ i, D (Finsupp.single i 1) ∈ Finsupp.supported R R {j | d j < d i} := by
    intro i
    have h := (Finsupp.supported R R {j | d j < d i}).neg_mem (hT i)
    simpa only [D, LinearMap.sub_apply, Module.End.one_apply, neg_sub] using h
  have h := bijective_one_sub_of_locallyNilpotent D
    (locallyNilpotent_of_degree_lowering d D hD)
  have heq : (1 - D : Module.End R (β →₀ R)) = T := by dsimp [D]; abel
  rwa [heq] at h

end TriangularInverse

section SymmetrizationEquivalence

variable {R L α : Type*} [CommRing R] [Algebra ℚ R]
variable [LieRing L] [LieAlgebra R L] [LinearOrder α]
variable (b : Module.Basis α R L)

/-- The average has the same top PBW term as the commutative monomial. -/
theorem symmetrization_basis_sub_mem_supported (m : α →₀ ℕ) :
    (pbwBasis b).repr (symmetrization b (b.symmetricAlgebra m)) - Finsupp.single m 1 ∈
      Finsupp.supported R R {j | (orderedWord j).length < (orderedWord m).length} := by
  classical
  let w := orderedWord m
  let ws (σ : Equiv.Perm (Fin w.length)) := List.ofFn (w.get ∘ σ)
  have hp (σ : Equiv.Perm (Fin w.length)) : (ws σ).Perm w := by
    simpa only [ws, List.ofFn_get] using σ.ofFn_comp_perm w.get
  have hi (σ : Equiv.Perm (Fin w.length)) : wordIndex (ws σ) = m :=
    (wordIndex_eq_iff_perm.mpr (hp σ)).trans (wordIndex_orderedWord m)
  have hl (σ : Equiv.Perm (Fin w.length)) : (ws σ).length = w.length :=
    (hp σ).length_eq
  have havg : (pbwBasis b).repr (symmetrization b (b.symmetricAlgebra m)) =
      inverseFactorial R w.length • ∑ σ : Equiv.Perm (Fin w.length),
        (pbwBasis b).repr (wordEval b (Finsupp.single (ws σ) 1)) := by
    rw [symmetrization_basis, averagedWord_map, averagedProduct_apply, map_smul, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro σ _
    congr 1
    rw [wordEval_single_one, List.map_ofFn]
    rfl
  rw [havg]
  have heq : inverseFactorial R w.length •
      (∑ σ : Equiv.Perm (Fin w.length),
        (pbwBasis b).repr (wordEval b (Finsupp.single (ws σ) 1))) - Finsupp.single m 1 =
      inverseFactorial R w.length • ∑ σ : Equiv.Perm (Fin w.length),
        ((pbwBasis b).repr (wordEval b (Finsupp.single (ws σ) 1)) - Finsupp.single m 1) := by
    rw [Finset.sum_sub_distrib, smul_sub, inverseFactorial_smul_sum_const]
  rw [heq]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro σ _
  simpa only [hi σ, hl σ] using
    pbwBasis_repr_wordEval_sub_single_mem_supported b (ws σ)

/-- Symmetrization in monomial and PBW coordinates. -/
def symmetrizationCoordinates : Module.End R ((α →₀ ℕ) →₀ R) :=
  (pbwBasis b).repr.toLinearMap.comp
    ((symmetrization b).comp b.symmetricAlgebra.repr.symm.toLinearMap)

@[simp] theorem symmetrizationCoordinates_single (m : α →₀ ℕ) :
    symmetrizationCoordinates b (Finsupp.single m 1) =
      (pbwBasis b).repr (symmetrization b (b.symmetricAlgebra m)) := by
  simp [symmetrizationCoordinates]

theorem symmetrizationCoordinates_bijective : Function.Bijective (symmetrizationCoordinates b) := by
  apply bijective_of_degree_triangular (fun m : α →₀ ℕ ↦ (orderedWord m).length)
  intro m
  rw [symmetrizationCoordinates_single]
  exact symmetrization_basis_sub_mem_supported b m

theorem symmetrization_bijective : Function.Bijective (symmetrization b) := by
  constructor
  · intro x y hxy
    apply b.symmetricAlgebra.repr.injective
    apply (symmetrizationCoordinates_bijective b).injective
    change (pbwBasis b).repr (symmetrization b (b.symmetricAlgebra.repr.symm
      (b.symmetricAlgebra.repr x))) =
      (pbwBasis b).repr (symmetrization b (b.symmetricAlgebra.repr.symm
        (b.symmetricAlgebra.repr y)))
    simp only [LinearEquiv.symm_apply_apply, hxy]
  · intro y
    obtain ⟨p, hp⟩ := (symmetrizationCoordinates_bijective b).surjective ((pbwBasis b).repr y)
    refine ⟨b.symmetricAlgebra.repr.symm p, (pbwBasis b).repr.injective ?_⟩
    exact hp

/-- The characteristic-zero PBW symmetrization equivalence, with inverse justified
by strict degree lowering and finite geometric sums. -/
def symmetrizationEquiv : SymmetricAlgebra R L ≃ₗ[R] UniversalEnvelopingAlgebra R L :=
  LinearEquiv.ofBijective (symmetrization b) (symmetrization_bijective b)

@[simp] theorem symmetrizationEquiv_apply (x : SymmetricAlgebra R L) :
    symmetrizationEquiv b x = symmetrization b x := rfl

@[simp] theorem symmetrizationEquiv_one : symmetrizationEquiv b 1 = 1 :=
  symmetrization_one b

@[simp] theorem symmetrizationEquiv_ι (x : L) :
    symmetrizationEquiv b (SymmetricAlgebra.ι R L x) = UniversalEnvelopingAlgebra.ι R x :=
  symmetrization_ι b x

@[simp] theorem symmetrizationEquiv_symm_ι (x : L) :
    (symmetrizationEquiv b).symm (UniversalEnvelopingAlgebra.ι R x) =
      SymmetricAlgebra.ι R L x := by
  rw [← symmetrizationEquiv_ι b x, LinearEquiv.symm_apply_apply]

theorem symmetrizationEquiv_prod (n : ℕ) (v : Fin n → L) :
    symmetrizationEquiv b ((List.ofFn (fun i ↦ SymmetricAlgebra.ι R L (v i))).prod) =
      inverseFactorial R n • ∑ σ : Equiv.Perm (Fin n),
        (List.ofFn (fun i ↦ UniversalEnvelopingAlgebra.ι R (v (σ i)))).prod := by
  rw [symmetrizationEquiv_apply, symmetrization_prod, averagedProduct_apply]
  rfl

end SymmetrizationEquivalence

end EnvelopingIsomorphism.PBW
