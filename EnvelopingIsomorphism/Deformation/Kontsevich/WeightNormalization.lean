import Mathlib.Algebra.Module.Rat
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
Geometric labelled weights include the outgoing-edge factorials, but no
internal-vertex factorial. The homogeneous MC coefficient uses W/n!; a family
with one distinguished input and n total vertices uses W/(n-1)!.

The low graph inputs use suspended-symmetric degree q-2 for a vertex with q
outgoing edges. Thus bivectors have degree zero and a distinguished vector or
trivector can be moved past bivectors with sign +1. The underlying signed DGLA
still has degree q-1, differential [mu,-], and gauge velocity [X,alpha]-dX.
No general conversion to a different skew L-infinity convention is asserted.
-/

namespace EnvelopingIsomorphism.Deformation.Kontsevich

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

/-- Effective homogeneous MC weights; the input is the geometric labelled weight. -/
def effectiveMCWeight (n : ℕ) (geoWeight : V) : V := (n.factorial : ℚ)⁻¹ • geoWeight

/-- One distinguished input among n total vertices. The impossible n=0 case is zero. -/
def distinguishedWeight : ℕ → V → V
  | 0, _ => 0
  | n + 1, geoWeight => (n.factorial : ℚ)⁻¹ • geoWeight

@[simp] theorem effectiveMCWeight_zero (w : V) : effectiveMCWeight 0 w = w := by
  simp [effectiveMCWeight]

@[simp] theorem effectiveMCWeight_one (w : V) : effectiveMCWeight 1 w = w := by
  simp [effectiveMCWeight]

@[simp] theorem distinguishedWeight_zero (w : V) : distinguishedWeight 0 w = 0 := rfl

@[simp] theorem distinguishedWeight_succ (n : ℕ) (w : V) :
    distinguishedWeight (n + 1) w = effectiveMCWeight n w := rfl

/-- Choosing the distinguished vertex accounts for exactly the missing factor n. -/
theorem distinguishedWeight_eq_smul_effective (n : ℕ) (w : V) :
    distinguishedWeight n w = (n : ℚ) • effectiveMCWeight n w := by
  cases n with
  | zero => simp
  | succ n =>
    rw [distinguishedWeight_succ, effectiveMCWeight, effectiveMCWeight, smul_smul]
    congr 1
    rw [Nat.factorial_succ, Nat.cast_mul]
    have hn : ((n + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    have hf : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    field_simp

theorem map_effectiveMCWeight (f : V →+ W) (n : ℕ) (w : V) :
    f (effectiveMCWeight n w) = effectiveMCWeight n (f w) := map_rat_smul f _ _

theorem map_distinguishedWeight (f : V →+ W) (n : ℕ) (w : V) :
    f (distinguishedWeight n w) = distinguishedWeight n (f w) := by
  cases n with
  | zero => exact map_zero f
  | succ n => exact map_rat_smul f _ _

def suspendedGraphDegree (q : ℕ) : ℤ := (q : ℤ) - 2

@[simp] theorem suspendedGraphDegree_vector : suspendedGraphDegree 1 = -1 := rfl
@[simp] theorem suspendedGraphDegree_bivector : suspendedGraphDegree 2 = 0 := rfl
@[simp] theorem suspendedGraphDegree_trivector : suspendedGraphDegree 3 = 1 := rfl

/-- No hidden mixed-input permutation sign occurs when crossing a bivector. -/
theorem suspendedGraphDegree_bivector_sign (q : ℕ) :
    (suspendedGraphDegree q * suspendedGraphDegree 2).negOnePow = 1 := by
  simp

end EnvelopingIsomorphism.Deformation.Kontsevich
