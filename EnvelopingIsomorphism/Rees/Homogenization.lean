import EnvelopingIsomorphism.Enveloping.Injective
import EnvelopingIsomorphism.Enveloping.BaseChange
import Mathlib.RingTheory.TensorProduct.Maps
import EnvelopingIsomorphism.Rees.HomogeneousBlocks
import EnvelopingIsomorphism.Rees.EnvelopingScalarCoordinates

/-!
# Homogenizing the Lie bracket and conjugating enveloping maps

The scaled bracket is a native Lie algebra for every scalar. A unit scalar gives an actual
Lie equivalence, hence an actual enveloping equivalence. All objects here are polynomial
algebra inputs; no identification with completed Laurent-polynomial function rings is made.
-/

noncomputable section

namespace EnvelopingIsomorphism.Rees

open Module
open scoped TensorProduct BigOperators

variable {R : Type*} [CommRing R]

/-- The original additive module, equipped below with the scalar-multiplied Lie bracket. -/
@[nolint unusedArguments]
def Scaled (_c : R) (L : Type*) [LieRing L] [LieAlgebra R L] := L

namespace Scaled

variable (c : R) (L : Type*) [LieRing L] [LieAlgebra R L]

instance : AddCommGroup (Scaled c L) := inferInstanceAs (AddCommGroup L)
instance : Module R (Scaled c L) := inferInstanceAs (Module R L)

/-- The scaling construction retains the original linear coordinates. -/
def toOriginal : Scaled c L ≃ₗ[R] L where
  toEquiv := Equiv.refl _
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance : Bracket (Scaled c L) (Scaled c L) where
  bracket x y := (toOriginal c L).symm (c • ⁅toOriginal c L x, toOriginal c L y⁆)

@[simp] theorem toOriginal_bracket (x y : Scaled c L) :
    toOriginal c L ⁅x, y⁆ = c • ⁅toOriginal c L x, toOriginal c L y⁆ := rfl

/-- Multiplying a Lie bracket by any central scalar preserves Jacobi. -/
instance : LieRing (Scaled c L) where
  add_lie x y z := (toOriginal c L).injective (by
    simp only [toOriginal_bracket, map_add, LieRing.add_lie, smul_add])
  lie_add x y z := (toOriginal c L).injective (by
    simp only [toOriginal_bracket, map_add, LieRing.lie_add, smul_add])
  lie_self x := (toOriginal c L).injective (by
    simp only [toOriginal_bracket, LieRing.lie_self, smul_zero, map_zero])
  leibniz_lie x y z := (toOriginal c L).injective (by
    simp only [toOriginal_bracket, map_add, smul_lie, lie_smul, smul_smul]
    rw [LieRing.leibniz_lie, smul_add])

instance : LieAlgebra R (Scaled c L) where
  lie_smul a x y := (toOriginal c L).injective (by
    simp only [toOriginal_bracket, map_smul, lie_smul, smul_smul, mul_comm])

variable {L}

/-- Transport the existing basis without changing its coordinates. -/
def basis {ι : Type*} (b : Basis ι R L) : Basis ι R (Scaled c L) :=
  b.map (toOriginal c L).symm

@[simp] theorem toOriginal_basis {ι : Type*} (b : Basis ι R L) (i : ι) :
    toOriginal c L (basis c b i) = b i := by simp [basis]

@[simp] theorem basis_repr {ι : Type*} (b : Basis ι R L) (x : Scaled c L) (i : ι) :
    (basis c b).repr x i = b.repr (toOriginal c L x) i := rfl

theorem structureCoeff {ι : Type*} (b : Basis ι R L) (i j r : ι) :
    (basis c b).repr ⁅basis c b i, basis c b j⁆ r = c * b.repr ⁅b i, b j⁆ r := by
  rw [basis_repr, toOriginal_bracket, toOriginal_basis, toOriginal_basis]
  simp

variable (L)

/-- If the scalar is a unit, `x ↦ c x` identifies the scaled Lie algebra with the original. -/
def scaleLieEquiv (u : Rˣ) : Scaled (u : R) L ≃ₗ⁅R⁆ L where
  __ := (toOriginal (u : R) L).trans (LinearEquiv.smulOfUnit u)
  map_lie' {x y} := by
    change (u : R) • ((u : R) • ⁅toOriginal (u : R) L x, toOriginal (u : R) L y⁆) =
      ⁅(u : R) • toOriginal (u : R) L x, (u : R) • toOriginal (u : R) L y⁆
    rw [smul_lie, lie_smul]

@[simp] theorem scaleLieEquiv_apply (u : Rˣ) (x : Scaled (u : R) L) :
    scaleLieEquiv L u x = (u : R) • toOriginal (u : R) L x := rfl

@[simp] theorem scaleLieEquiv_symm_apply (u : Rˣ) (x : L) :
    (scaleLieEquiv L u).symm x = (toOriginal (u : R) L).symm ((u⁻¹ : Rˣ) • x) := rfl

section BaseChange

variable (S : Type*) [CommRing S] [Algebra R S]

/-- Scaling the bracket commutes with extending the coefficient ring. -/
theorem baseChange_toOriginal_bracket (x y : S ⊗[R] Scaled c L) :
    ((toOriginal c L).baseChange R S _ _) ⁅x, y⁆ =
      algebraMap R S c •
        ⁅((toOriginal c L).baseChange R S _ _) x, ((toOriginal c L).baseChange R S _ _) y⁆ := by
  induction x using TensorProduct.induction_on with
  | zero =>
      have hz : ⁅(0 : S ⊗[R] Scaled c L), y⁆ = 0 :=
        (AddMonoidHom.mk' (fun z : S ⊗[R] Scaled c L ↦ ⁅z, y⁆)
          (fun z z' ↦ LieRing.add_lie z z' y)).map_zero
      simp [hz]
  | tmul a x =>
      induction y using TensorProduct.induction_on with
      | zero =>
          have hz : ⁅a ⊗ₜ[R] x, (0 : S ⊗[R] Scaled c L)⁆ = 0 :=
            (AddMonoidHom.mk' (fun z : S ⊗[R] Scaled c L ↦ ⁅a ⊗ₜ[R] x, z⁆)
              (fun z z' ↦ LieRing.lie_add _ z z')).map_zero
          simp [hz]
      | tmul b y =>
          simp only [LieAlgebra.ExtendScalars.bracket_tmul, LinearEquiv.baseChange_tmul,
            toOriginal_bracket]
          rw [TensorProduct.tmul_smul, IsScalarTower.algebraMap_smul]
      | add y z hy hz => simp only [LieRing.lie_add, map_add, smul_add, hy, hz]
  | add x z hx hz => simp only [LieRing.add_lie, map_add, smul_add, hx, hz]

/-- The actual native equivalence between scaling before and after scalar extension. -/
def baseChangeLieEquiv :
    S ⊗[R] Scaled c L ≃ₗ⁅S⁆ Scaled (algebraMap R S c) (S ⊗[R] L) where
  __ := ((toOriginal c L).baseChange R S _ _).trans
    (toOriginal (algebraMap R S c) (S ⊗[R] L)).symm
  map_lie' {x y} := by
    apply (toOriginal (algebraMap R S c) (S ⊗[R] L)).injective
    change ((toOriginal c L).baseChange R S _ _) ⁅x, y⁆ =
      algebraMap R S c •
        ⁅((toOriginal c L).baseChange R S _ _) x, ((toOriginal c L).baseChange R S _ _) y⁆
    exact baseChange_toOriginal_bracket c L S x y

@[simp] theorem baseChangeLieEquiv_tmul (a : S) (x : Scaled c L) :
    toOriginal (algebraMap R S c) (S ⊗[R] L)
      (baseChangeLieEquiv c L S (a ⊗ₜ[R] x)) = a ⊗ₜ[R] toOriginal c L x := rfl

end BaseChange

end Scaled

namespace Homogenization

/-- Integer powers of a chosen unit, regarded as coefficients in the original ring. -/
def unitPower (u : Rˣ) (n : ℤ) : R := (u ^ n : Rˣ)

@[simp] theorem unitPower_zero (u : Rˣ) : unitPower u 0 = 1 := by simp [unitPower]
@[simp] theorem unitPower_one (u : Rˣ) : unitPower u 1 = u := by simp [unitPower]
@[simp] theorem unitPower_nat (u : Rˣ) (n : ℕ) : unitPower u n = (u : R) ^ n := by
  simp [unitPower]

theorem unitPower_add (u : Rˣ) (a b : ℤ) :
    unitPower u (a + b) = unitPower u a * unitPower u b := by
  simp [unitPower, zpow_add]

theorem unitPower_neg_mul (u : Rˣ) (a : ℤ) : unitPower u (-a) * unitPower u a = 1 := by
  rw [← unitPower_add, neg_add_cancel, unitPower_zero]

/-- A uniform scalar on the generators contributes one scalar factor for each letter. -/
theorem map_word_scaled {A B α : Type*} [Ring A] [Algebra R A] [Ring B] [Algebra R B]
    (f : A →ₐ[R] B) (v : α → A) (w : α → B) (c : R)
    (h : ∀ i, f (v i) = c • w i) (s : List α) :
    f ((s.map v).prod) = c ^ s.length • (s.map w).prod := by
  induction s with
  | nil => simp
  | cons i s ih =>
      simp only [List.map_cons, List.prod_cons, map_mul, h, ih, List.length_cons]
      rw [smul_mul_smul_comm, pow_succ, mul_comm]

theorem repr_diagonal {X Y α : Type*} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (bX : Basis α R X) (bY : Basis α R Y)
    (f : X →ₗ[R] Y) (a : α → R) (hf : ∀ i, f (bX i) = a i • bY i) (x : X) (i : α) :
    bY.repr (f x) i = a i * bX.repr x i := by
  classical
  have he : (bY.coord i).comp f = a i • bX.coord i := by
    apply bX.ext
    intro j
    by_cases hji : j = i
    · subst j
      simp [hf, Basis.coord_apply]
    · simp [hf, Basis.coord_apply, hji]
  simpa only [LinearMap.comp_apply, Basis.coord_apply, LinearMap.smul_apply, smul_eq_mul] using
    LinearMap.congr_fun he x

variable {L M α β : Type*} [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

/-- The actual enveloping equivalence induced by multiplying the scaled Lie generators by a unit. -/
def scaleEnveloping (u : Rˣ) (L : Type*) [LieRing L] [LieAlgebra R L] :
    UniversalEnvelopingAlgebra R (Scaled (u : R) L) ≃ₐ[R] UniversalEnvelopingAlgebra R L :=
  EnvelopingIsomorphism.Enveloping.congr (Scaled.scaleLieEquiv L u)

@[simp] theorem scaleEnveloping_ι (u : Rˣ) (x : Scaled (u : R) L) :
    scaleEnveloping u L (UniversalEnvelopingAlgebra.ι R x) =
      (u : R) • UniversalEnvelopingAlgebra.ι R (Scaled.toOriginal (u : R) L x) := by
  rw [scaleEnveloping, EnvelopingIsomorphism.Enveloping.congr_ι, Scaled.scaleLieEquiv_apply,
    map_smul]

/-- Conjugate an arbitrary associative equivalence by the two actual unit-scaling maps. -/
def conjugate (u : Rˣ)
    (Φ : UniversalEnvelopingAlgebra R L ≃ₐ[R] UniversalEnvelopingAlgebra R M) :
    UniversalEnvelopingAlgebra R (Scaled (u : R) L) ≃ₐ[R]
      UniversalEnvelopingAlgebra R (Scaled (u : R) M) :=
  (scaleEnveloping u L).trans (Φ.trans (scaleEnveloping u M).symm)

@[simp] theorem conjugate_apply (u : Rˣ)
    (Φ : UniversalEnvelopingAlgebra R L ≃ₐ[R] UniversalEnvelopingAlgebra R M)
    (x : UniversalEnvelopingAlgebra R (Scaled (u : R) L)) :
    conjugate u Φ x = (scaleEnveloping u M).symm (Φ (scaleEnveloping u L x)) := rfl

variable [LinearOrder α] [LinearOrder β]

theorem length_orderedWord_eq_degree (m : α →₀ ℕ) :
    (PBW.orderedWord m).length = m.degree := by
  rw [PBW.length_orderedWord]
  rfl

theorem scaleEnveloping_pbwBasis (u : Rˣ) (b : Basis α R L) (m : α →₀ ℕ) :
    scaleEnveloping u L (PBW.pbwBasis (Scaled.basis (u : R) b) m) =
      unitPower u (m.degree : ℤ) • PBW.pbwBasis b m := by
  rw [PBW.pbwBasis_apply, PBW.pbwBasis_apply, unitPower_nat, ← length_orderedWord_eq_degree]
  apply map_word_scaled (scaleEnveloping u L).toAlgHom
  intro i
  simp only [Function.comp_apply, AlgEquiv.coe_toAlgHom, scaleEnveloping_ι, Scaled.toOriginal_basis]

theorem scaleEnveloping_symm_pbwBasis (u : Rˣ) (b : Basis α R L) (m : α →₀ ℕ) :
    (scaleEnveloping u L).symm (PBW.pbwBasis b m) =
      unitPower u (-(m.degree : ℤ)) • PBW.pbwBasis (Scaled.basis (u : R) b) m := by
  apply (scaleEnveloping u L).injective
  rw [AlgEquiv.apply_symm_apply, map_smul, scaleEnveloping_pbwBasis, smul_smul,
    unitPower_neg_mul, one_smul]

theorem coeff_scaleEnveloping_symm (u : Rˣ) (b : Basis α R L)
    (x : UniversalEnvelopingAlgebra R L) (m : α →₀ ℕ) :
    (PBW.pbwBasis (Scaled.basis (u : R) b)).repr ((scaleEnveloping u L).symm x) m =
      unitPower u (-(m.degree : ℤ)) * (PBW.pbwBasis b).repr x m :=
  repr_diagonal (PBW.pbwBasis b) (PBW.pbwBasis (Scaled.basis (u : R) b))
    (scaleEnveloping u L).symm.toAlgHom.toLinearMap _ (scaleEnveloping_symm_pbwBasis u b) x m

/-- The exact ordered-PBW coefficient formula, in every input/output degree. -/
theorem conjugate_pbw_coefficient (u : Rˣ) (bL : Basis α R L) (bM : Basis β R M)
    (Φ : UniversalEnvelopingAlgebra R L ≃ₐ[R] UniversalEnvelopingAlgebra R M)
    (a : α →₀ ℕ) (m : β →₀ ℕ) :
    (PBW.pbwBasis (Scaled.basis (u : R) bM)).repr
      (conjugate u Φ (PBW.pbwBasis (Scaled.basis (u : R) bL) a)) m =
      unitPower u ((a.degree : ℤ) - (m.degree : ℤ)) *
        (PBW.pbwBasis bM).repr (Φ (PBW.pbwBasis bL a)) m := by
  rw [conjugate_apply, scaleEnveloping_pbwBasis, map_smul, map_smul, map_smul,
    Finsupp.smul_apply, smul_eq_mul, coeff_scaleEnveloping_symm, ← mul_assoc,
    ← unitPower_add]
  rw [sub_eq_add_neg]

/-- On Lie generators, the coefficient in output PBW degree `m` is multiplied by `u^(1-m)`. -/
theorem conjugate_generator_coefficient (u : Rˣ) (bL : Basis α R L) (bM : Basis β R M)
    (Φ : UniversalEnvelopingAlgebra R L ≃ₐ[R] UniversalEnvelopingAlgebra R M)
    (i : α) (m : β →₀ ℕ) :
    (PBW.pbwBasis (Scaled.basis (u : R) bM)).repr
      (conjugate u Φ (UniversalEnvelopingAlgebra.ι R (Scaled.basis (u : R) bL i))) m =
      unitPower u (1 - (m.degree : ℤ)) *
        (PBW.pbwBasis bM).repr (Φ (UniversalEnvelopingAlgebra.ι R (bL i))) m := by
  simpa only [PBW.pbwBasis_single, Finsupp.degree_single, Nat.cast_one] using
    conjugate_pbw_coefficient u bL bM Φ (Finsupp.single i 1) m

section Symmetrization

variable [Algebra ℚ R]

/-- The actual permutation-averaged PBW basis, transported from the existing symmetric algebra. -/
def symBasis (b : Basis α R L) : Basis (α →₀ ℕ) R (UniversalEnvelopingAlgebra R L) :=
  b.symmetricAlgebra.map (PBW.symmetrizationEquiv b)

@[simp] theorem symBasis_apply (b : Basis α R L) (m : α →₀ ℕ) :
    symBasis b m = PBW.symmetrizationEquiv b (b.symmetricAlgebra m) := by
  simp [symBasis]

omit [Algebra ℚ R] in
theorem symmetricMap_scale_basis (u : Rˣ) (b : Basis α R L) (m : α →₀ ℕ) :
    EnvelopingIsomorphism.Enveloping.symmetricMap (Scaled.scaleLieEquiv L u).toLieHom.toLinearMap
      ((Scaled.basis (u : R) b).symmetricAlgebra m) =
        unitPower u (m.degree : ℤ) • b.symmetricAlgebra m := by
  have hs := PBW.symmetricAlgebra_basis_wordIndex (Scaled.basis (u : R) b) (PBW.orderedWord m)
  have ht := PBW.symmetricAlgebra_basis_wordIndex b (PBW.orderedWord m)
  rw [PBW.wordIndex_orderedWord] at hs ht
  rw [hs, ht, unitPower_nat, ← length_orderedWord_eq_degree]
  apply map_word_scaled
  intro i
  simp only [Function.comp_apply, EnvelopingIsomorphism.Enveloping.symmetricMap_ι,
    LieHom.coe_toLinearMap, LieEquiv.coe_toLieHom, Scaled.scaleLieEquiv_apply,
    Scaled.toOriginal_basis, map_smul]

/-- Unit scaling acts diagonally on actual symmetrization, by its homogeneous degree. -/
theorem scaleEnveloping_symBasis (u : Rˣ) (b : Basis α R L) (m : α →₀ ℕ) :
    scaleEnveloping u L (symBasis (Scaled.basis (u : R) b) m) =
      unitPower u (m.degree : ℤ) • symBasis b m := by
  change EnvelopingIsomorphism.Enveloping.map (Scaled.scaleLieEquiv L u).toLieHom
    (PBW.symmetrization (Scaled.basis (u : R) b) ((Scaled.basis (u : R) b).symmetricAlgebra m)) =
      unitPower u (m.degree : ℤ) • PBW.symmetrization b (b.symmetricAlgebra m)
  rw [EnvelopingIsomorphism.Enveloping.symmetrization_natural (Scaled.basis (u : R) b) b,
    symmetricMap_scale_basis, map_smul]

theorem scaleEnveloping_symm_symBasis (u : Rˣ) (b : Basis α R L) (m : α →₀ ℕ) :
    (scaleEnveloping u L).symm (symBasis b m) =
      unitPower u (-(m.degree : ℤ)) • symBasis (Scaled.basis (u : R) b) m := by
  apply (scaleEnveloping u L).injective
  rw [AlgEquiv.apply_symm_apply, map_smul, scaleEnveloping_symBasis, smul_smul,
    unitPower_neg_mul, one_smul]

theorem coeff_scaleEnveloping_symm_sym (u : Rˣ) (b : Basis α R L)
    (x : UniversalEnvelopingAlgebra R L) (m : α →₀ ℕ) :
    (symBasis (Scaled.basis (u : R) b)).repr ((scaleEnveloping u L).symm x) m =
      unitPower u (-(m.degree : ℤ)) * (symBasis b).repr x m :=
  repr_diagonal (symBasis b) (symBasis (Scaled.basis (u : R) b))
    (scaleEnveloping u L).symm.toAlgHom.toLinearMap _ (scaleEnveloping_symm_symBasis u b) x m

/-- The conjugated map has the exact factor `u^(input degree - output degree)` in symmetrized
coordinates. These are the actual PBW averaging maps, rather than abstract chosen linear maps. -/
theorem conjugate_sym_coefficient (u : Rˣ) (bL : Basis α R L) (bM : Basis β R M)
    (Φ : UniversalEnvelopingAlgebra R L ≃ₐ[R] UniversalEnvelopingAlgebra R M)
    (a : α →₀ ℕ) (m : β →₀ ℕ) :
    (symBasis (Scaled.basis (u : R) bM)).repr
      (conjugate u Φ (symBasis (Scaled.basis (u : R) bL) a)) m =
      unitPower u ((a.degree : ℤ) - (m.degree : ℤ)) *
        (symBasis bM).repr (Φ (symBasis bL a)) m := by
  rw [conjugate_apply, scaleEnveloping_symBasis, map_smul, map_smul, map_smul,
    Finsupp.smul_apply, smul_eq_mul, coeff_scaleEnveloping_symm_sym, ← mul_assoc,
    ← unitPower_add]
  rw [sub_eq_add_neg]

/-- Actual PBW symmetrization expressed on the standard polynomial coordinates of a basis. -/
def symPolynomialEquiv (b : Basis α R L) :
    MvPolynomial α R ≃ₗ[R] UniversalEnvelopingAlgebra R L :=
  (SymmetricAlgebra.equivMvPolynomial b).symm.toLinearEquiv.trans (PBW.symmetrizationEquiv b)

@[simp] theorem symPolynomialEquiv_monomial (b : Basis α R L) (m : α →₀ ℕ) :
    symPolynomialEquiv b (MvPolynomial.monomial m 1) = symBasis b m := by
  simp [symPolynomialEquiv, symBasis, Basis.symmetricAlgebra]

/-- The polynomial coordinate map uses the actual normalized permutation average on products. -/
theorem symPolynomialEquiv_prod (b : Basis α R L) (n : ℕ) (v : Fin n → L) :
    symPolynomialEquiv b ((SymmetricAlgebra.equivMvPolynomial b)
      ((List.ofFn (fun i ↦ SymmetricAlgebra.ι R L (v i))).prod)) =
        PBW.inverseFactorial R n • ∑ σ : Equiv.Perm (Fin n),
          (List.ofFn (fun i ↦ UniversalEnvelopingAlgebra.ι R (v (σ i)))).prod := by
  change PBW.symmetrizationEquiv b ((SymmetricAlgebra.equivMvPolynomial b).symm
    ((SymmetricAlgebra.equivMvPolynomial b) _)) = _
  rw [AlgEquiv.symm_apply_apply]
  exact PBW.symmetrizationEquiv_prod b n v

theorem coeff_symPolynomialEquiv_symm (b : Basis α R L)
    (x : UniversalEnvelopingAlgebra R L) (m : α →₀ ℕ) :
    MvPolynomial.coeff m ((symPolynomialEquiv b).symm x) = (symBasis b).repr x m := rfl

/-- The polynomial-coordinate linear map obtained from an actual enveloping equivalence. -/
def symPolynomialMap (bL : Basis α R L) (bM : Basis β R M)
    (Φ : UniversalEnvelopingAlgebra R L ≃ₐ[R] UniversalEnvelopingAlgebra R M) :
    MvPolynomial α R →ₗ[R] MvPolynomial β R :=
  ((symPolynomialEquiv bL).trans (Φ.toLinearEquiv.trans (symPolynomialEquiv bM).symm)).toLinearMap

theorem coeff_symPolynomialMap_monomial (bL : Basis α R L) (bM : Basis β R M)
    (Φ : UniversalEnvelopingAlgebra R L ≃ₐ[R] UniversalEnvelopingAlgebra R M)
    (a : α →₀ ℕ) (m : β →₀ ℕ) :
    MvPolynomial.coeff m (symPolynomialMap bL bM Φ (MvPolynomial.monomial a 1)) =
      (symBasis bM).repr (Φ (symBasis bL a)) m := by
  change MvPolynomial.coeff m ((symPolynomialEquiv bM).symm
    (Φ (symPolynomialEquiv bL (MvPolynomial.monomial a 1)))) = _
  rw [symPolynomialEquiv_monomial, coeff_symPolynomialEquiv_symm]

/-- Exact homogeneous-block identity on native multivariate polynomial components. -/
theorem homogeneous_sym_block (u : Rˣ) (bL : Basis α R L) (bM : Basis β R M)
    (Φ : UniversalEnvelopingAlgebra R L ≃ₐ[R] UniversalEnvelopingAlgebra R M) (n m : ℕ) :
    (MvPolynomial.homogeneousComponent m).comp
        ((symPolynomialMap (Scaled.basis (u : R) bL) (Scaled.basis (u : R) bM) (conjugate u Φ)).comp
          (MvPolynomial.homogeneousComponent n)) =
      unitPower u ((n : ℤ) - (m : ℤ)) •
        ((MvPolynomial.homogeneousComponent m).comp
          ((symPolynomialMap bL bM Φ).comp (MvPolynomial.homogeneousComponent n))) := by
  apply HomogeneousBlocks.homogeneousComponent_comp
  intro a q
  rw [coeff_symPolynomialMap_monomial, coeff_symPolynomialMap_monomial]
  exact conjugate_sym_coefficient u bL bM Φ a q

end Symmetrization

section ScalarExtension

variable (S : Type*) [CommRing S] [Algebra R S]

/-- First extend the original associative equivalence, then perform the actual unit conjugation. -/
def baseChangedConjugate (u : Sˣ)
    (Φ : UniversalEnvelopingAlgebra R L ≃ₐ[R] UniversalEnvelopingAlgebra R M) :
    UniversalEnvelopingAlgebra S (Scaled (u : S) (S ⊗[R] L)) ≃ₐ[S]
      UniversalEnvelopingAlgebra S (Scaled (u : S) (S ⊗[R] M)) :=
  conjugate u (EnvelopingScalarCoordinates.baseChangeAlgEquiv R S Φ)

/-- The coefficient formula after genuine scalar extension, with original coefficients mapped
by the scalar algebra map. -/
theorem baseChangedConjugate_pbw_coefficient (u : Sˣ) (bL : Basis α R L) (bM : Basis β R M)
    (Φ : UniversalEnvelopingAlgebra R L ≃ₐ[R] UniversalEnvelopingAlgebra R M)
    (a : α →₀ ℕ) (m : β →₀ ℕ) :
    (PBW.pbwBasis (Scaled.basis (u : S) (bM.baseChange S))).repr
      (baseChangedConjugate S u Φ (PBW.pbwBasis (Scaled.basis (u : S) (bL.baseChange S)) a)) m =
      unitPower u ((a.degree : ℤ) - (m.degree : ℤ)) *
        algebraMap R S ((PBW.pbwBasis bM).repr (Φ (PBW.pbwBasis bL a)) m) := by
  rw [baseChangedConjugate, conjugate_pbw_coefficient,
    EnvelopingScalarCoordinates.pbwCoeff_baseChangeAlgEquiv]

/-- The `u^(1-degree)` formula on each generator after extending the coefficient ring. -/
theorem baseChangedConjugate_generator_coefficient (u : Sˣ) (bL : Basis α R L) (bM : Basis β R M)
    (Φ : UniversalEnvelopingAlgebra R L ≃ₐ[R] UniversalEnvelopingAlgebra R M)
    (i : α) (m : β →₀ ℕ) :
    (PBW.pbwBasis (Scaled.basis (u : S) (bM.baseChange S))).repr
      (baseChangedConjugate S u Φ
        (UniversalEnvelopingAlgebra.ι S (Scaled.basis (u : S) (bL.baseChange S) i))) m =
      unitPower u (1 - (m.degree : ℤ)) *
        algebraMap R S ((PBW.pbwBasis bM).repr (Φ (UniversalEnvelopingAlgebra.ι R (bL i))) m) := by
  simpa only [PBW.pbwBasis_single, Finsupp.degree_single, Nat.cast_one] using
    baseChangedConjugate_pbw_coefficient S u bL bM Φ (Finsupp.single i 1) m

/-- The finite PBW sum is the actual image of a generator under the homogenized equivalence. -/
theorem baseChangedConjugate_generator_formula (u : Sˣ) (bL : Basis α R L) (bM : Basis β R M)
    (Φ : UniversalEnvelopingAlgebra R L ≃ₐ[R] UniversalEnvelopingAlgebra R M) (i : α) :
    baseChangedConjugate S u Φ
        (UniversalEnvelopingAlgebra.ι S (Scaled.basis (u : S) (bL.baseChange S) i)) =
      ((PBW.pbwBasis bM).repr (Φ (UniversalEnvelopingAlgebra.ι R (bL i)))).sum
        (fun m a ↦ (unitPower u (1 - (m.degree : ℤ)) * algebraMap R S a) •
          PBW.pbwBasis (Scaled.basis (u : S) (bM.baseChange S)) m) := by
  classical
  apply (PBW.pbwBasis (Scaled.basis (u : S) (bM.baseChange S))).ext_elem
  intro q
  rw [baseChangedConjugate_generator_coefficient]
  simp only [Finsupp.sum, map_sum, map_smul, Basis.repr_self,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
  split_ifs with hq
  · rfl
  · rw [Finsupp.notMem_support_iff.mp hq, map_zero, mul_zero]

variable [Algebra ℚ S]

/-- The homogeneous symmetrization block identity for the actual scalar-extended equivalence. -/
theorem baseChanged_homogeneous_sym_block (u : Sˣ) (bL : Basis α R L) (bM : Basis β R M)
    (Φ : UniversalEnvelopingAlgebra R L ≃ₐ[R] UniversalEnvelopingAlgebra R M) (n m : ℕ) :
    (MvPolynomial.homogeneousComponent m).comp
        ((symPolynomialMap (Scaled.basis (u : S) (bL.baseChange S))
          (Scaled.basis (u : S) (bM.baseChange S)) (baseChangedConjugate S u Φ)).comp
            (MvPolynomial.homogeneousComponent n)) =
      unitPower u ((n : ℤ) - (m : ℤ)) •
        ((MvPolynomial.homogeneousComponent m).comp
          ((symPolynomialMap (bL.baseChange S) (bM.baseChange S)
            (EnvelopingScalarCoordinates.baseChangeAlgEquiv R S Φ)).comp
              (MvPolynomial.homogeneousComponent n))) :=
  homogeneous_sym_block u (bL.baseChange S) (bM.baseChange S)
    (EnvelopingScalarCoordinates.baseChangeAlgEquiv R S Φ) n m

end ScalarExtension

end Homogenization

end EnvelopingIsomorphism.Rees
