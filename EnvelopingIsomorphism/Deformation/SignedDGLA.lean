import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Algebra.Lie.Basic

/-!
Differential graded Lie algebras with the Koszul sign convention, indexed by
integer cohomological degrees.  The differential is the differential of an
actual Mathlib cochain complex.  This is distinct from an ordinary internally
graded Lie algebra, whose skew symmetry has no Koszul sign.
-/

namespace EnvelopingIsomorphism.Deformation

universe u v
variable (R : Type u) [CommRing R]

def gradedModuleCongr (V : ℤ → ModuleCat.{v} R) {p q : ℤ} (h : p = q) : V p ≃ₗ[R] V q :=
  h ▸ LinearEquiv.refl R (V p)

@[simp] theorem gradedModuleCongr_self (V : ℤ → ModuleCat.{v} R) (p : ℤ) (f : V p) :
    gradedModuleCongr R V rfl f = f := rfl

@[simp] theorem gradedModuleCongr_trans (V : ℤ → ModuleCat.{v} R) {p q r : ℤ}
    (h : p = q) (h' : q = r) (f : V p) :
    gradedModuleCongr R V h' (gradedModuleCongr R V h f) =
      gradedModuleCongr R V (h.trans h') f := by
  subst q
  subst r
  rfl

/-- A signed differential graded Lie algebra over a commutative ring. -/
structure SignedDGLA where
  complex : CochainComplex (ModuleCat.{v} R) ℤ
  bracket : (p q : ℤ) → complex.X p →ₗ[R] complex.X q →ₗ[R] complex.X (p + q)
  skew (p q : ℤ) (f : complex.X p) (g : complex.X q) :
    HEq (bracket p q f g) (-((p * q).negOnePow : R) • bracket q p g f)
  jacobi (p q r : ℤ) (f : complex.X p) (g : complex.X q) (h : complex.X r) :
    gradedModuleCongr R complex.X (add_assoc p q r).symm (bracket p (q + r) f (bracket q r g h)) =
      bracket (p + q) r (bracket p q f g) h +
        ((p * q).negOnePow : R) • gradedModuleCongr R complex.X
          (by omega : q + (p + r) = (p + q) + r) (bracket q (p + r) g (bracket p r f h))
  differential_bracket (p q : ℤ) (f : complex.X p) (g : complex.X q) :
    (complex.d (p + q) ((p + q) + 1)).hom (bracket p q f g) =
      gradedModuleCongr R complex.X (by omega : (p + 1) + q = (p + q) + 1)
        (bracket (p + 1) q ((complex.d p (p + 1)).hom f) g) +
      (p.negOnePow : R) • gradedModuleCongr R complex.X (add_assoc p q 1).symm
        (bracket p (q + 1) f ((complex.d q (q + 1)).hom g))

namespace SignedDGLA

variable {R} (D : SignedDGLA.{u, v} R)

abbrev Obj (p : ℤ) : Type v := D.complex.X p

def d (p : ℤ) : D.Obj p →ₗ[R] D.Obj (p + 1) := (D.complex.d p (p + 1)).hom

theorem d_sq (p : ℤ) (f : D.Obj p) : D.d (p + 1) (D.d p f) = 0 := by
  have hs := D.complex.d_comp_d p (p + 1) ((p + 1) + 1)
  exact congrArg (fun φ => φ.hom f) hs

theorem bracket_cast_right {p q q' : ℤ} (hq : q = q') (f : D.Obj p) (g : D.Obj q) :
    D.bracket p q' f (gradedModuleCongr R D.complex.X hq g) =
      gradedModuleCongr R D.complex.X (congrArg (p + ·) hq) (D.bracket p q f g) := by
  subst q'
  rfl

/-- Adjoint action of the ordinary degree-zero Lie algebra on each graded component. -/
def zeroAction (p : ℤ) : D.Obj 0 →ₗ[R] Module.End R (D.Obj p) :=
  (D.bracket 0 p).compr₂ (gradedModuleCongr R D.complex.X (zero_add p)).toLinearMap

theorem zeroAction_comp (p : ℤ) (X Y : D.Obj 0) (f : D.Obj p) :
    D.zeroAction p X (D.zeroAction p Y f) =
      gradedModuleCongr R D.complex.X (by omega : 0 + (0 + p) = p)
        (D.bracket 0 (0 + p) X (D.bracket 0 p Y f)) := by
  change gradedModuleCongr R D.complex.X (zero_add p)
      (D.bracket 0 p X (gradedModuleCongr R D.complex.X (zero_add p) (D.bracket 0 p Y f))) = _
  rw [D.bracket_cast_right, gradedModuleCongr_trans]

/-- The degree-zero component has the ordinary commutator signs. -/
theorem bracket_zero_skew (X Y : D.Obj 0) : D.bracket 0 0 X Y = -D.bracket 0 0 Y X := by
  have hs := eq_of_heq (D.skew 0 0 X Y)
  simp only [Int.mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one] at hs
  exact hs.trans (neg_one_smul R _)

theorem bracket_zero_jacobi (X Y Z : D.Obj 0) :
    D.bracket 0 0 X (D.bracket 0 0 Y Z) =
      D.bracket 0 0 (D.bracket 0 0 X Y) Z + D.bracket 0 0 Y (D.bracket 0 0 X Z) := by
  have hj := D.jacobi 0 0 0 X Y Z
  simp only [Int.mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one] at hj
  change D.bracket 0 0 X (D.bracket 0 0 Y Z) =
    D.bracket 0 0 (D.bracket 0 0 X Y) Z + (1 : R) • D.bracket 0 0 Y (D.bracket 0 0 X Z) at hj
  rw [one_smul] at hj
  exact hj

end SignedDGLA

namespace SignedDGLA

variable {K : Type u} [Field K] [CharZero K] (D : SignedDGLA.{u, v} K)

theorem bracket_zero_self (X : D.Obj 0) : D.bracket 0 0 X X = 0 := by
  have hs : (2 : K) • D.bracket 0 0 X X = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp (D.bracket_zero_skew X X)
  change (2 : K) • (D.bracket 0 0 X X : D.Obj 0) = 0 at hs
  have hi := congrArg (fun v : D.Obj 0 => (2 : K)⁻¹ • v) hs
  change (2 : K)⁻¹ • ((2 : K) • (D.bracket 0 0 X X : D.Obj 0)) =
    (2 : K)⁻¹ • (0 : D.Obj 0) at hi
  rw [smul_smul, inv_mul_cancel₀ (show (2 : K) ≠ 0 from two_ne_zero), one_smul, smul_zero] at hi
  exact hi

/-- The gauge degree is an ordinary Lie ring; odd-degree signs have disappeared. -/
@[reducible] def degreeZeroLieRing : LieRing (D.Obj 0) where
  toAddCommGroup := inferInstance
  bracket := fun X Y => D.bracket 0 0 X Y
  add_lie X Y Z := by
    change D.bracket 0 0 (X + Y) Z = D.bracket 0 0 X Z + D.bracket 0 0 Y Z
    rw [map_add, LinearMap.add_apply]
  lie_add X Y Z := (D.bracket 0 0 X).map_add Y Z
  lie_self := D.bracket_zero_self
  leibniz_lie := D.bracket_zero_jacobi

/-- The degree-zero ordinary Lie ring inherits its scalar-linear Lie algebra structure. -/
@[reducible] def degreeZeroLieAlgebra :
    letI := D.degreeZeroLieRing
    LieAlgebra K (D.Obj 0) := by
  letI := D.degreeZeroLieRing
  exact { (inferInstance : Module K (D.Obj 0)) with
    lie_smul := fun r X Y => by
      change D.bracket 0 0 X (r • Y) = r • D.bracket 0 0 X Y
      exact (D.bracket 0 0 X).map_smul r Y }

end SignedDGLA

end EnvelopingIsomorphism.Deformation
