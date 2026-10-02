import EnvelopingIsomorphism.FieldTheory.CoefficientField
import EnvelopingIsomorphism.Enveloping.BaseChange
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Algebra.Lie.Solvable

/-! Lie algebras over a field containing their finite structure coefficients. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.FieldTheory.LieModel

open scoped BigOperators TensorProduct

variable {k L : Type*} [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
  {n : ℕ} (b : Module.Basis (Fin n) k L) (K : IntermediateField ℚ k)
  (hK : ∀ i j a, b.repr ⁅b i, b j⁆ a ∈ K)

/-- Coordinates over the smaller field, tagged by their structure coefficients
so that Lean infers the correct Lie bracket on the coordinate module. -/
@[nolint unusedArguments]
def Model (_b : Module.Basis (Fin n) k L) (K : IntermediateField ℚ k)
    (_hK : ∀ i j a, _b.repr ⁅_b i, _b j⁆ a ∈ K) : Type _ := Fin n → K

instance : AddCommGroup (Model b K hK) := inferInstanceAs (AddCommGroup (Fin n → K))
instance : Module K (Model b K hK) := inferInstanceAs (Module K (Fin n → K))
instance : FiniteDimensional K (Model b K hK) :=
  inferInstanceAs (FiniteDimensional K (Fin n → K))

/-- The standard finite coordinate basis of the descended Lie algebra. -/
def basis : Module.Basis (Fin n) K (Model b K hK) := Pi.basisFun K (Fin n)

/-- The actual coordinates of the bracket, regarded as elements of `K`. -/
def coefficient (i j a : Fin n) : K := ⟨b.repr ⁅b i, b j⁆ a, hK i j a⟩

@[simp] theorem coefficient_coe (i j a : Fin n) :
    (coefficient b K hK i j a : k) = b.repr ⁅b i, b j⁆ a := rfl

/-- Coordinates evaluated in the original Lie algebra, as a map over `K`. -/
def includeLinear : Model b K hK →ₗ[K] RestrictScalars K k L where
  toFun x := ∑ i, (x i : k) • b i
  map_add' x y := by
    change (∑ i, ((x i + y i : K) : k) • b i) =
      (∑ i, (x i : k) • b i) + ∑ i, (y i : k) • b i
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' r x := by
    change (∑ i, ((r * x i : K) : k) • b i) = (r : k) • ∑ i, (x i : k) • b i
    simp [Finset.smul_sum, smul_smul]

theorem includeLinear_apply (x : Model b K hK) :
    includeLinear b K hK x = (∑ i, (x i : k) • b i : L) := rfl

@[simp] theorem repr_includeLinear (x : Model b K hK) (a : Fin n) :
    b.repr (includeLinear b K hK x) a = (x a : k) := by
  simp [includeLinear, map_sum, map_smul, Finsupp.single_apply]

theorem includeLinear_injective : Function.Injective (includeLinear b K hK) := by
  intro x y h
  funext a
  apply Subtype.ext
  have ha := congrArg (fun z : L ↦ b.repr z a) h
  simpa only [repr_includeLinear] using ha

@[simp] theorem includeLinear_basis (i : Fin n) :
    includeLinear b K hK (basis b K hK i) = (b i : L) := by
  apply b.ext_elem
  intro a
  rw [repr_includeLinear]
  change (((Pi.basisFun K (Fin n)) i a : K) : k) = b.repr (b i) a
  rw [Pi.basisFun_apply]
  simp [Finsupp.single_apply, Pi.single_apply, apply_ite, eq_comm]

/-- Bilinear bracket with the descended structure coefficients. -/
def modelBracket (x y : Model b K hK) : Model b K hK :=
  fun a ↦ ∑ i, ∑ j, x i * y j * coefficient b K hK i j a

theorem includeLinear_bracket (x y : Model b K hK) :
    includeLinear b K hK (modelBracket b K hK x y) =
      ⁅includeLinear b K hK x, includeLinear b K hK y⁆ := by
  apply b.ext_elem
  intro a
  rw [repr_includeLinear]
  dsimp only [Model] at x y
  change ((∑ i, ∑ j, x i * y j * coefficient b K hK i j a : K) : k) =
    b.repr ⁅∑ i, (x i : k) • b i, ∑ j, (y j : k) • b j⁆ a
  simp [sum_lie, lie_sum, smul_lie, lie_smul, coefficient_coe,
    map_sum, map_smul, smul_eq_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

instance : LieRing (Model b K hK) where
  bracket := modelBracket b K hK
  add_lie x y z := by
    apply includeLinear_injective b K hK
    change includeLinear b K hK (modelBracket b K hK (x + y) z) =
      includeLinear b K hK (modelBracket b K hK x z + modelBracket b K hK y z)
    simp only [includeLinear_bracket, map_add, add_lie]
  lie_add x y z := by
    apply includeLinear_injective b K hK
    change includeLinear b K hK (modelBracket b K hK x (y + z)) =
      includeLinear b K hK (modelBracket b K hK x y + modelBracket b K hK x z)
    simp only [includeLinear_bracket, map_add, lie_add]
  lie_self x := by
    apply includeLinear_injective b K hK
    change includeLinear b K hK (modelBracket b K hK x x) = includeLinear b K hK 0
    rw [includeLinear_bracket, lie_self, map_zero]
  leibniz_lie x y z := by
    apply includeLinear_injective b K hK
    change includeLinear b K hK (modelBracket b K hK x (modelBracket b K hK y z)) =
      includeLinear b K hK
        (modelBracket b K hK (modelBracket b K hK x y) z +
          modelBracket b K hK y (modelBracket b K hK x z))
    simp only [includeLinear_bracket, map_add]
    exact leibniz_lie _ _ _

instance : LieAlgebra K (Model b K hK) where
  lie_smul r x y := by
    apply includeLinear_injective b K hK
    change includeLinear b K hK (modelBracket b K hK x (r • y)) =
      includeLinear b K hK (r • modelBracket b K hK x y)
    simp only [includeLinear_bracket, map_smul, lie_smul]

/-- An actual injective Lie map into the original algebra restricted to `K`. -/
def includeLie : Model b K hK →ₗ⁅K⁆ RestrictScalars K k L where
  toLinearMap := includeLinear b K hK
  map_lie' := includeLinear_bracket b K hK _ _

/-- Underlying inclusion into the original carrier, with original `k`-scalars. -/
def includeValue (x : Model b K hK) : L :=
  RestrictScalars.addEquiv K k L (includeLinear b K hK x)

@[simp] theorem repr_includeValue (x : Model b K hK) (i : Fin n) :
    b.repr (includeValue b K hK x) i = (x i : k) := repr_includeLinear b K hK x i

@[simp] theorem includeValue_basis (i : Fin n) : includeValue b K hK (basis b K hK i) = b i :=
  congrArg (RestrictScalars.addEquiv K k L) (includeLinear_basis b K hK i)

theorem includeValue_bracket (x y : Model b K hK) :
    includeValue b K hK ⁅x, y⁆ = ⁅includeValue b K hK x, includeValue b K hK y⁆ :=
  congrArg (RestrictScalars.addEquiv K k L) (includeLinear_bracket b K hK x y)

@[simp] theorem basis_repr (x : Model b K hK) (i : Fin n) :
    (basis b K hK).repr x i = x i := by
  change (Pi.basisFun K (Fin n)).repr (x : Fin n → K) i = x i
  rw [← Module.Basis.equivFun_apply, Pi.basisFun_equivFun]
  rfl

@[simp] theorem basis_bracket_repr (i j a : Fin n) :
    (basis b K hK).repr ⁅basis b K hK i, basis b K hK j⁆ a = coefficient b K hK i j a := by
  apply Subtype.ext
  rw [basis_repr, coefficient_coe]
  have h := congrArg (fun z : L ↦ b.repr z a)
    (includeValue_bracket b K hK (basis b K hK i) (basis b K hK j))
  simpa only [repr_includeValue, includeValue_basis] using h

theorem finrank_model : Module.finrank K (Model b K hK) = n := by
  rw [Module.finrank_eq_card_basis (basis b K hK), Fintype.card_fin]

/-- Extending the descended coordinate basis gives the original basis. -/
def baseChangeLinearEquiv : k ⊗[K] Model b K hK ≃ₗ[k] L :=
  (Algebra.TensorProduct.basis k (basis b K hK)).equiv b (Equiv.refl _)

@[simp] theorem baseChangeLinearEquiv_one_tmul_basis (i : Fin n) :
    baseChangeLinearEquiv b K hK (1 ⊗ₜ[K] basis b K hK i) = b i := by
  simpa only [baseChangeLinearEquiv, Algebra.TensorProduct.basis_apply, Equiv.refl_apply] using
    Module.Basis.equiv_apply (Algebra.TensorProduct.basis k (basis b K hK)) i b (Equiv.refl _)

theorem baseChangeLinearEquiv_tmul (a : k) (x : Model b K hK) :
    baseChangeLinearEquiv b K hK (a ⊗ₜ[K] x) =
      a • includeValue b K hK x := by
  apply b.ext_elem
  intro i
  simp [baseChangeLinearEquiv, Module.Basis.equiv, Algebra.TensorProduct.basis_repr_tmul,
    repr_includeValue, basis_repr]

local instance : Module k (RestrictScalars K k L) := RestrictScalars.moduleOrig K k L
local instance : LieAlgebra k (RestrictScalars K k L) := inferInstanceAs (LieAlgebra k L)

/-- The scalar-extension Lie homomorphism supplied by the native tensor lift. -/
def baseChangeHom : k ⊗[K] Model b K hK →ₗ⁅k⁆ L :=
  EnvelopingIsomorphism.Enveloping.lieLiftBaseChange (A := RestrictScalars K k L)
    k (includeLie b K hK)

theorem baseChangeHom_eq :
    (baseChangeHom b K hK).toLinearMap = (baseChangeLinearEquiv b K hK).toLinearMap := by
  apply (Algebra.TensorProduct.basis k (basis b K hK)).ext
  intro i
  rw [Algebra.TensorProduct.basis_apply]
  change EnvelopingIsomorphism.Enveloping.lieLiftBaseChange (A := RestrictScalars K k L) k (includeLie b K hK)
      (1 ⊗ₜ[K] basis b K hK i) = baseChangeLinearEquiv b K hK (1 ⊗ₜ[K] basis b K hK i)
  rw [EnvelopingIsomorphism.Enveloping.lieLiftBaseChange_tmul, one_smul,
    baseChangeLinearEquiv_one_tmul_basis]
  exact includeLinear_basis b K hK i

/-- Scalar extension of the descended Lie algebra is the original Lie algebra. -/
def baseChangeEquiv : k ⊗[K] Model b K hK ≃ₗ⁅k⁆ L :=
  LieEquiv.ofBijective (baseChangeHom b K hK) (by
    change Function.Bijective (baseChangeHom b K hK).toLinearMap
    rw [baseChangeHom_eq]
    exact (baseChangeLinearEquiv b K hK).bijective)

@[simp] theorem baseChangeEquiv_tmul_basis (a : k) (i : Fin n) :
    baseChangeEquiv b K hK (a ⊗ₜ[K] basis b K hK i) = a • b i := by
  change (baseChangeHom b K hK).toLinearMap (a ⊗ₜ[K] basis b K hK i) = _
  rw [baseChangeHom_eq]
  change baseChangeLinearEquiv b K hK (a ⊗ₜ[K] basis b K hK i) = _
  rw [baseChangeLinearEquiv_tmul, includeValue_basis]

@[simp] theorem baseChangeEquiv_one_tmul_basis (i : Fin n) :
    baseChangeEquiv b K hK (1 ⊗ₜ[K] basis b K hK i) = b i := by
  rw [baseChangeEquiv_tmul_basis, one_smul]

instance [LieAlgebra.IsSolvable L] : LieAlgebra.IsSolvable (Model b K hK) := by
  letI : LieAlgebra.IsSolvable (RestrictScalars K k L) :=
    inferInstanceAs (LieAlgebra.IsSolvable L)
  exact Function.Injective.lieAlgebra_isSolvable
    (f := includeLie b K hK) (includeLinear_injective b K hK)

end EnvelopingIsomorphism.FieldTheory.LieModel
