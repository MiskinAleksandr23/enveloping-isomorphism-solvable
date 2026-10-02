import Mathlib.Algebra.Lie.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.RingTheory.LaurentSeries
import EnvelopingIsomorphism.Poisson.FirstJet

/-!
# The weighted Rees Lie family

The structural support condition is input from an adapted filtered basis. The new Jacobi
identity is reflected through the injective Laurent scaling map; it is not an input.
-/

noncomputable section

namespace EnvelopingIsomorphism.Rees

open Module
open scoped TensorProduct BigOperators

variable {k ι L : Type*} [Field k] [Fintype ι] [DecidableEq ι]
    [LieRing L] [LieAlgebra k L]

local instance laurentBaseModule : Module k (LaurentSeries k) := Algebra.toModule

/-- An adapted weight system, including its already-proved structural support condition. -/
structure WeightData (b : Basis ι k L) where
  weight : ι → ℕ
  compatible : ∀ i j r, b.repr ⁅b i, b j⁆ r ≠ 0 → weight i + weight j ≤ weight r

namespace WeightData

variable {b : Basis ι k L} (d : WeightData b)

/-- The polynomial structure coefficient of the Rees family. -/
def coeff (i j r : ι) : Polynomial k :=
  Polynomial.C (b.repr ⁅b i, b j⁆ r) *
    Polynomial.X ^ (d.weight r - (d.weight i + d.weight j))

/-- The diagonal factor in the comparison with the original Lie algebra. -/
def scale (i : ι) : LaurentSeries k := HahnSeries.single (-(d.weight i : ℤ)) 1

omit [Fintype ι] [DecidableEq ι] in
theorem scale_ne_zero (i : ι) : d.scale i ≠ 0 := by
  simp [scale]

omit [Fintype ι] [DecidableEq ι] in
theorem coeff_scale (i j r : ι) :
    algebraMap (Polynomial k) (LaurentSeries k) (d.coeff i j r) * d.scale r =
      d.scale i * d.scale j * algebraMap k (LaurentSeries k) (b.repr ⁅b i, b j⁆ r) := by
  by_cases hc : b.repr ⁅b i, b j⁆ r = 0
  · simp [coeff, hc]
  · have hw := d.compatible i j r hc
    have he : ((d.weight r - (d.weight i + d.weight j) : ℕ) : ℤ) + -(d.weight r : ℤ) =
        -(d.weight i : ℤ) + -(d.weight j : ℤ) := by omega
    have hm : algebraMap k (LaurentSeries k) (b.repr ⁅b i, b j⁆ r) =
        HahnSeries.C (b.repr ⁅b i, b j⁆ r) := by
      simp [HahnSeries.algebraMap_apply']
    rw [hm]
    simp [coeff, scale, Polynomial.algebraMap_hahnSeries_apply, HahnSeries.C_apply,
      HahnSeries.single_mul_single, he]

omit [Fintype ι] [DecidableEq ι] in
/-- At parameter zero, precisely the coefficients of exact weight survive. -/
theorem coeff_eval_zero (i j r : ι) :
    Polynomial.eval 0 (d.coeff i j r) =
      if d.weight r = d.weight i + d.weight j then b.repr ⁅b i, b j⁆ r else 0 := by
  by_cases hc : b.repr ⁅b i, b j⁆ r = 0
  · simp [coeff, hc]
  · have hw := d.compatible i j r hc
    by_cases he : d.weight r = d.weight i + d.weight j
    · simp [coeff, he]
    · have hd : d.weight r - (d.weight i + d.weight j) ≠ 0 := by omega
      simp [coeff, he, hd]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem coeff_eval_one (i j r : ι) :
    Polynomial.eval 1 (d.coeff i j r) = b.repr ⁅b i, b j⁆ r := by
  simp [coeff]

end WeightData

/-- The Rees module is a type synonym for the usual finite free polynomial module. -/
@[nolint unusedArguments]
def Family {b : Basis ι k L} (_d : WeightData b) := ι → Polynomial k

namespace Family

variable {b : Basis ι k L} (d : WeightData b)

instance : AddCommGroup (Family d) := inferInstanceAs (AddCommGroup (ι → Polynomial k))
instance : Module (Polynomial k) (Family d) :=
  inferInstanceAs (Module (Polynomial k) (ι → Polynomial k))

/-- The existing coordinate module and the Rees module have identical linear structure. -/
def coordinates : Family d ≃ₗ[Polynomial k] (ι → Polynomial k) where
  toEquiv := Equiv.refl _
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The original coordinate indexing gives an actual polynomial basis. -/
def basis : Basis ι (Polynomial k) (Family d) :=
  (Pi.basisFun (Polynomial k) ι).map (coordinates d).symm

instance : Module.Free (Polynomial k) (Family d) := Module.Free.of_basis (basis d)
instance : Module.Finite (Polynomial k) (Family d) := Module.Finite.of_basis (basis d)

omit [DecidableEq ι] in
@[simp] theorem basis_repr (x : Family d) (i : ι) :
    (basis d).repr x i = coordinates d x i := by
  simp [basis]

@[simp] theorem coordinates_basis (i : ι) : coordinates d (basis d i) = Pi.single i 1 := by
  simp [basis]

instance : Bracket (Family d) (Family d) where
  bracket x y := (coordinates d).symm
    (fun r ↦ ∑ i, ∑ j, coordinates d x i * coordinates d y j * d.coeff i j r)

omit [DecidableEq ι] in
@[simp] theorem coordinates_bracket (x y : Family d) (r : ι) :
    coordinates d ⁅x, y⁆ r =
      ∑ i, ∑ j, coordinates d x i * coordinates d y j * d.coeff i j r := rfl

/-- The injective comparison map sends the `i`th generator to `t^(-w_i) b_i`. -/
def embed : Family d →+ LaurentSeries k ⊗[k] L where
  toFun x := (b.baseChange (LaurentSeries k)).equivFun.symm
    (fun i ↦ algebraMap (Polynomial k) (LaurentSeries k) (coordinates d x i) * d.scale i)
  map_zero' := by simp only [map_zero, Pi.zero_apply, zero_mul]; exact map_zero _
  map_add' x y := by
    apply (b.baseChange (LaurentSeries k)).equivFun.injective
    simp only [map_add, LinearEquiv.apply_symm_apply]
    funext i
    simp only [Pi.add_apply, map_add, add_mul]

omit [DecidableEq ι] in
@[simp] theorem repr_embed (x : Family d) (i : ι) :
    (b.baseChange (LaurentSeries k)).repr (embed d x) i =
      algebraMap (Polynomial k) (LaurentSeries k) (coordinates d x i) * d.scale i := by
  change (b.baseChange (LaurentSeries k)).equivFun (embed d x) i = _
  exact congrFun ((b.baseChange (LaurentSeries k)).equivFun.apply_symm_apply _) i

omit [DecidableEq ι] in
theorem embed_injective : Function.Injective (embed d) := by
  intro x y h
  apply (coordinates d).injective
  funext i
  have he := congrArg (fun z ↦ (b.baseChange (LaurentSeries k)).repr z i) h
  simp only [repr_embed] at he
  apply Polynomial.algebraMap_hahnSeries_injective (R := k) ℤ
  exact mul_right_cancel₀ (d.scale_ne_zero i) he

omit [DecidableEq ι] in
/-- Coordinates of the original scalar-extended Lie bracket. -/
theorem repr_lie (x y : LaurentSeries k ⊗[k] L) (r : ι) :
    (b.baseChange (LaurentSeries k)).repr ⁅x, y⁆ r =
      ∑ i, ∑ j, (b.baseChange (LaurentSeries k)).repr x i *
        (b.baseChange (LaurentSeries k)).repr y j *
        algebraMap k (LaurentSeries k) (b.repr ⁅b i, b j⁆ r) := by
  let bE := b.baseChange (LaurentSeries k)
  change bE.repr ⁅x, y⁆ r = _
  conv_lhs => rw [← bE.sum_repr x, ← bE.sum_repr y, sum_lie_sum]
  simp [bE, smul_lie, lie_smul, map_sum, Algebra.smul_def, mul_assoc, mul_left_comm]

omit [DecidableEq ι] in
/-- Polynomial Rees brackets match the original bracket after Laurent scaling. -/
theorem embed_bracket (x y : Family d) : embed d ⁅x, y⁆ = ⁅embed d x, embed d y⁆ := by
  apply (b.baseChange (LaurentSeries k)).ext_elem
  intro r
  rw [repr_embed, repr_lie]
  simp only [coordinates_bracket, map_sum, map_mul, Finset.sum_mul, repr_embed]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_assoc, d.coeff_scale]
  ac_rfl

/-- Jacobi is proved by the injective comparison with the original Lie algebra. -/
instance : LieRing (Family d) where
  add_lie x y z := (embed_injective d) (by
    simp only [embed_bracket, map_add]
    exact LieRing.add_lie _ _ _)
  lie_add x y z := (embed_injective d) (by
    simp only [embed_bracket, map_add]
    exact LieRing.lie_add _ _ _)
  lie_self x := (embed_injective d) (by simp only [embed_bracket, map_zero, lie_self])
  leibniz_lie x y z := (embed_injective d) (by
    simp only [embed_bracket, map_add]
    exact LieRing.leibniz_lie _ _ _)

instance : LieAlgebra (Polynomial k) (Family d) where
  lie_smul a x y := by
    apply (coordinates d).injective
    ext r
    simp [Finset.mul_sum, mul_assoc, mul_left_comm]

/-- The displayed polynomial coefficients are precisely the family's structure coefficients. -/
theorem basis_bracket (i j : ι) :
    ⁅basis d i, basis d j⁆ = ∑ r, d.coeff i j r • basis d r := by
  apply (coordinates d).injective
  ext r
  simp [Pi.single_apply]

/-- The coefficient formula survives arbitrary scalar extension of the polynomial family. -/
theorem baseChange_structureCoeff {A : Type*} [CommRing A] [Algebra (Polynomial k) A]
    (i j r : ι) :
    ((basis d).baseChange A).repr
      ⁅(basis d).baseChange A i, (basis d).baseChange A j⁆ r =
        algebraMap (Polynomial k) A (d.coeff i j r) := by
  simp [LieAlgebra.ExtendScalars.bracket_tmul, Algebra.smul_def, Pi.single_apply]

/-- The original Lie algebra extended to the Laurent coefficient field. -/
abbrev Original := LaurentSeries k ⊗[k] L

/-- The Rees Lie algebra after extending scalars to a ring in which the parameter is invertible. -/
abbrev GenericFiber := LaurentSeries k ⊗[Polynomial k] Family d

/-- A basis of the original scalar extension with the prescribed diagonal rescaling. -/
def scaledBasis : Basis ι (LaurentSeries k) (Original (k := k) (L := L)) :=
  (b.baseChange (LaurentSeries k)).unitsSMul (fun i ↦ Units.mk0 (d.scale i) (d.scale_ne_zero i))

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem scaledBasis_apply (i : ι) :
    scaledBasis d i = d.scale i • (b.baseChange (LaurentSeries k) i) := by
  simp [scaledBasis, Basis.unitsSMul_apply, Units.smul_def]

/-- The diagonal comparison after the parameter has been inverted, as an actual linear equivalence. -/
def scaleLinearEquiv : GenericFiber d ≃ₗ[LaurentSeries k] Original (k := k) (L := L) :=
  ((basis d).baseChange (LaurentSeries k)).equiv (scaledBasis d) (Equiv.refl ι)

omit [DecidableEq ι] in
@[simp] theorem scaleLinearEquiv_basis (i : ι) :
    scaleLinearEquiv d ((basis d).baseChange (LaurentSeries k) i) =
      d.scale i • (b.baseChange (LaurentSeries k) i) := by
  rw [scaleLinearEquiv, Basis.equiv_apply, Equiv.refl_apply, scaledBasis_apply]

omit [DecidableEq ι] in
theorem repr_scaleLinearEquiv (x : GenericFiber d) (i : ι) :
    (scaledBasis d).repr (scaleLinearEquiv d x) i =
      ((basis d).baseChange (LaurentSeries k)).repr x i := by
  simp [scaleLinearEquiv, Basis.equiv]

omit [DecidableEq ι] in
/-- The equivalence extends precisely the injective comparison used to prove Jacobi. -/
theorem scaleLinearEquiv_one_tmul (x : Family d) :
    scaleLinearEquiv d ((1 : LaurentSeries k) ⊗ₜ[Polynomial k] x) = embed d x := by
  apply (scaledBasis d).ext_elem
  intro i
  rw [repr_scaleLinearEquiv]
  simp [scaledBasis, repr_embed, Units.smul_def, Algebra.smul_def,
    mul_comm, d.scale_ne_zero i]

/-- After inverting the parameter, the Rees family is the original scalar-extended Lie algebra. -/
def scaleLieEquiv : GenericFiber d ≃ₗ⁅LaurentSeries k⁆ Original (k := k) (L := L) where
  __ := scaleLinearEquiv d
  map_lie' {x y} := by
    apply EnvelopingIsomorphism.Poisson.map_lie_of_basis
      ((basis d).baseChange (LaurentSeries k)) (scaleLinearEquiv d).toLinearMap
    intro i j
    simp only [Basis.baseChange_apply, LieAlgebra.ExtendScalars.bracket_tmul, one_mul,
      LinearEquiv.coe_coe, scaleLinearEquiv_one_tmul]
    exact embed_bracket d _ _

omit [DecidableEq ι] in
/-- The scalar-extended equivalence has exactly the diagonal formula required in D2. -/
@[simp] theorem scaleLieEquiv_basis (i : ι) :
    scaleLieEquiv d ((1 : LaurentSeries k) ⊗ₜ[Polynomial k] basis d i) =
      d.scale i ⊗ₜ[k] b i := by
  change scaleLinearEquiv d ((1 : LaurentSeries k) ⊗ₜ[Polynomial k] basis d i) = _
  simpa only [Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
    scaleLinearEquiv_basis d i

/-- Evaluate the polynomial parameter at a chosen scalar. -/
@[reducible] def evaluationAlgebra (a : k) : Algebra (Polynomial k) k :=
  (Polynomial.evalRingHom a).toAlgebra

/-- The genuine scalar-extension fiber of the Rees family at a parameter value. -/
def Fiber (a : k) : Type _ :=
  letI := evaluationAlgebra (k := k) a
  k ⊗[Polynomial k] Family d

instance (a : k) : LieRing (Fiber d a) := by
  letI := evaluationAlgebra (k := k) a
  exact LieAlgebra.ExtendScalars.instLieRing (R := Polynomial k) (A := k) (L := Family d)

instance (a : k) : LieAlgebra k (Fiber d a) := by
  letI := evaluationAlgebra (k := k) a
  exact LieAlgebra.ExtendScalars.instLieAlgebra (R := Polynomial k) (A := k) (L := Family d)

/-- The finite basis on every actual special fiber. -/
def fiberBasis (a : k) : Basis ι k (Fiber d a) := by
  letI := evaluationAlgebra (k := k) a
  exact (basis d).baseChange k

instance (a : k) : Module.Finite k (Fiber d a) := Module.Finite.of_basis (fiberBasis d a)

theorem fiber_structureCoeff (a : k) (i j r : ι) :
    (fiberBasis d a).repr ⁅fiberBasis d a i, fiberBasis d a j⁆ r =
      Polynomial.eval a (d.coeff i j r) := by
  letI := evaluationAlgebra (k := k) a
  exact baseChange_structureCoeff d i j r

/-- At zero, the native fiber has exactly the associated-graded structure coefficients. -/
theorem zeroFiber_structureCoeff (i j r : ι) :
    (fiberBasis d 0).repr ⁅fiberBasis d 0 i, fiberBasis d 0 j⁆ r =
      if d.weight r = d.weight i + d.weight j then b.repr ⁅b i, b j⁆ r else 0 := by
  rw [fiber_structureCoeff, d.coeff_eval_zero]

/-- At one, the structure coefficients are those of the original algebra. -/
theorem oneFiber_structureCoeff (i j r : ι) :
    (fiberBasis d 1).repr ⁅fiberBasis d 1 i, fiberBasis d 1 j⁆ r = b.repr ⁅b i, b j⁆ r := by
  rw [fiber_structureCoeff, d.coeff_eval_one]

/-- The fiber at one is the original native Lie algebra, with its prescribed basis. -/
def oneFiberLieEquiv : Fiber d 1 ≃ₗ⁅k⁆ L where
  __ := (fiberBasis d 1).equiv b (Equiv.refl ι)
  map_lie' {x y} := by
    apply EnvelopingIsomorphism.Poisson.map_lie_of_basis (fiberBasis d 1)
    intro i j
    apply b.ext_elem
    intro r
    rw [LinearEquiv.coe_coe, Basis.equiv_apply, Basis.equiv_apply]
    simpa [Basis.equiv] using oneFiber_structureCoeff d i j r

@[simp] theorem oneFiberLieEquiv_basis (i : ι) :
    oneFiberLieEquiv d (fiberBasis d 1 i) = b i := by
  change ((fiberBasis d 1).equiv b (Equiv.refl ι)) (fiberBasis d 1 i) = b i
  exact Basis.equiv_apply _ _ _ _

/-- Equal constant structure coefficients identify two zero fibers by the prescribed basis map. -/
def zeroFiberLieEquiv {M : Type*} [LieRing M] [LieAlgebra k M]
    {c : Basis ι k M} (e : WeightData c)
    (h : ∀ i j r, Polynomial.eval 0 (d.coeff i j r) = Polynomial.eval 0 (e.coeff i j r)) :
    Fiber d 0 ≃ₗ⁅k⁆ Fiber e 0 where
  __ := (fiberBasis d 0).equiv (fiberBasis e 0) (Equiv.refl ι)
  map_lie' {x y} := by
    apply EnvelopingIsomorphism.Poisson.map_lie_of_basis (fiberBasis d 0)
    intro i j
    apply (fiberBasis e 0).ext_elem
    intro r
    rw [LinearEquiv.coe_coe, Basis.equiv_apply, Basis.equiv_apply]
    have hh : (fiberBasis d 0).repr ⁅fiberBasis d 0 i, fiberBasis d 0 j⁆ r =
        (fiberBasis e 0).repr ⁅fiberBasis e 0 i, fiberBasis e 0 j⁆ r := by
      rw [fiber_structureCoeff, fiber_structureCoeff, h]
    simpa [Basis.equiv] using hh

@[simp] theorem zeroFiberLieEquiv_basis {M : Type*} [LieRing M] [LieAlgebra k M]
    {c : Basis ι k M} (e : WeightData c)
    (h : ∀ i j r, Polynomial.eval 0 (d.coeff i j r) = Polynomial.eval 0 (e.coeff i j r))
    (i : ι) : zeroFiberLieEquiv d e h (fiberBasis d 0 i) = fiberBasis e 0 i := by
  change ((fiberBasis d 0).equiv (fiberBasis e 0) (Equiv.refl ι)) (fiberBasis d 0 i) = _
  exact Basis.equiv_apply _ _ _ _

end Family

end EnvelopingIsomorphism.Rees
