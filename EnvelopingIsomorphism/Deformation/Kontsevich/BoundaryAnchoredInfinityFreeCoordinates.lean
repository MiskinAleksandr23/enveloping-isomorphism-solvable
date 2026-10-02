import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryAnchoredInfinityTopology
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Fintype.Card

/-! Free infinity coordinates with the inner complex anchor and the single outside real anchor removed. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration Topology

abbrev BoundaryAnchoredInfinityFreeInterior {n : ℕ} (a : Fin n) := {j : Fin n // j ≠ a}
abbrev BoundaryAnchoredInfinityFreeBoundary {m : ℕ} (o : Fin m) := {j : Fin m // j ≠ o}

abbrev BoundaryAnchoredInfinityFreeCoordinates {n : ℕ} (a : Fin n) (m : ℕ) (o : Fin m) :=
  (BoundaryAnchoredInfinityFreeInterior a → ℂ) × (BoundaryAnchoredInfinityFreeBoundary o → ℝ) × ℝ

theorem card_boundaryAnchoredInfinityFreeInterior {n : ℕ} (a : Fin n) :
    Fintype.card (BoundaryAnchoredInfinityFreeInterior a) = n - 1 := by
  have h : Fintype.card (BoundaryAnchoredInfinityFreeInterior a) = (Finset.univ.erase a).card := by
    apply Fintype.card_of_subtype
    intro j
    simp
  rw [h, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]

theorem card_boundaryAnchoredInfinityFreeBoundary {m : ℕ} (o : Fin m) :
    Fintype.card (BoundaryAnchoredInfinityFreeBoundary o) = m - 1 :=
  card_boundaryAnchoredInfinityFreeInterior o

theorem finrank_boundaryAnchoredInfinityFreeCoordinates {n m : ℕ} (a : Fin n) (o : Fin m) :
    Module.finrank ℝ (BoundaryAnchoredInfinityFreeCoordinates a m o) = 2 * n + m - 2 := by
  change Module.finrank ℝ ((BoundaryAnchoredInfinityFreeInterior a → ℂ) ×
    (BoundaryAnchoredInfinityFreeBoundary o → ℝ) × ℝ) = _
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_pi_fintype]
  simp only [Complex.finrank_real_complex, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, card_boundaryAnchoredInfinityFreeInterior,
    mul_one]
  have hn : 1 ≤ n := by have := a.isLt; omega
  have hm : 1 ≤ m := by have := o.isLt; omega
  omega

namespace BoundaryAnchoredInfinityFreeCoordinates

variable {n m : ℕ} {a : Fin n} {o : Fin m}

def radius (x : BoundaryAnchoredInfinityFreeCoordinates a m o) : ℝ := x.2.2

def shape (x : BoundaryAnchoredInfinityFreeCoordinates a m o) (j : Fin n) : ℂ :=
  if hj : j = a then Complex.I else x.1 ⟨j, hj⟩

/-- A free boundary slot stores an inner velocity or an outer coarse position; the outside anchor is fixed. -/
def boundaryCoordinate (l : Fin (m + 1)) (x : BoundaryAnchoredInfinityFreeCoordinates a m o) (j : Fin m) : ℝ :=
  if hj : j = o then BoundaryAnchoredInfinityData.referenceSign l o else x.2.1 ⟨j, hj⟩

def boundaryBase (l u : Fin (m + 1)) (x : BoundaryAnchoredInfinityFreeCoordinates a m o) (j : Fin m) : ℝ :=
  if j ∈ boundaryClusterBlock l u then 0 else x.boundaryCoordinate l j

def boundaryVelocity (l u : Fin (m + 1)) (x : BoundaryAnchoredInfinityFreeCoordinates a m o) (j : Fin m) : ℝ :=
  if j ∈ boundaryClusterBlock l u then x.boundaryCoordinate l j else 0

def parameters (l u : Fin (m + 1)) (x : BoundaryAnchoredInfinityFreeCoordinates a m o) :
    BoundaryAnchoredInfinityParameterSpace n m :=
  (x.shape, x.boundaryBase l u, x.boundaryVelocity l u)

@[simp] theorem shape_anchor (x : BoundaryAnchoredInfinityFreeCoordinates a m o) :
    x.shape a = Complex.I := by simp [shape]

@[simp] theorem shape_free (x : BoundaryAnchoredInfinityFreeCoordinates a m o)
    (j : BoundaryAnchoredInfinityFreeInterior a) : x.shape j = x.1 j := by
  simp only [shape, dif_neg j.property]

@[simp] theorem boundaryCoordinate_anchor (l : Fin (m + 1)) (x : BoundaryAnchoredInfinityFreeCoordinates a m o) :
    x.boundaryCoordinate l o = BoundaryAnchoredInfinityData.referenceSign l o := by simp [boundaryCoordinate]

@[simp] theorem boundaryCoordinate_free (l : Fin (m + 1)) (x : BoundaryAnchoredInfinityFreeCoordinates a m o)
    (j : BoundaryAnchoredInfinityFreeBoundary o) : x.boundaryCoordinate l j = x.2.1 j := by
  simp only [boundaryCoordinate, dif_neg j.property]

@[fun_prop] theorem contDiff_radius :
    ContDiff ℝ ⊤ (radius : BoundaryAnchoredInfinityFreeCoordinates a m o → ℝ) := by
  unfold radius
  fun_prop

@[fun_prop] theorem contDiff_shape (j : Fin n) :
    ContDiff ℝ ⊤ (fun x : BoundaryAnchoredInfinityFreeCoordinates a m o => x.shape j) := by
  unfold shape
  split_ifs <;> fun_prop

@[fun_prop] theorem contDiff_boundaryCoordinate (l : Fin (m + 1)) (j : Fin m) :
    ContDiff ℝ ⊤ (fun x : BoundaryAnchoredInfinityFreeCoordinates a m o => x.boundaryCoordinate l j) := by
  unfold boundaryCoordinate
  split_ifs <;> fun_prop

@[fun_prop] theorem contDiff_boundaryBase (l u : Fin (m + 1)) (j : Fin m) :
    ContDiff ℝ ⊤ (fun x : BoundaryAnchoredInfinityFreeCoordinates a m o => x.boundaryBase l u j) := by
  unfold boundaryBase
  split_ifs <;> fun_prop

@[fun_prop] theorem contDiff_boundaryVelocity (l u : Fin (m + 1)) (j : Fin m) :
    ContDiff ℝ ⊤ (fun x : BoundaryAnchoredInfinityFreeCoordinates a m o => x.boundaryVelocity l u j) := by
  unfold boundaryVelocity
  split_ifs <;> fun_prop

@[fun_prop] theorem contDiff_parameters (l u : Fin (m + 1)) :
    ContDiff ℝ ⊤ (parameters (a := a) (o := o) l u) :=
  (contDiff_pi.mpr contDiff_shape).prodMk
    ((contDiff_pi.mpr (contDiff_boundaryBase l u)).prodMk
      (contDiff_pi.mpr (contDiff_boundaryVelocity l u)))

@[fun_prop] theorem continuous_radius :
    Continuous (radius : BoundaryAnchoredInfinityFreeCoordinates a m o → ℝ) := contDiff_radius.continuous

@[fun_prop] theorem continuous_shape (j : Fin n) :
    Continuous (fun x : BoundaryAnchoredInfinityFreeCoordinates a m o => x.shape j) :=
  (contDiff_shape j).continuous

@[fun_prop] theorem continuous_boundaryBase (l u : Fin (m + 1)) (j : Fin m) :
    Continuous (fun x : BoundaryAnchoredInfinityFreeCoordinates a m o => x.boundaryBase l u j) :=
  (contDiff_boundaryBase l u j).continuous

@[fun_prop] theorem continuous_boundaryVelocity (l u : Fin (m + 1)) (j : Fin m) :
    Continuous (fun x : BoundaryAnchoredInfinityFreeCoordinates a m o => x.boundaryVelocity l u j) :=
  (contDiff_boundaryVelocity l u j).continuous

@[fun_prop] theorem continuous_parameters (l u : Fin (m + 1)) :
    Continuous (parameters (a := a) (o := o) l u) := (contDiff_parameters l u).continuous

theorem closed_conditions (x : BoundaryAnchoredInfinityFreeCoordinates a m o) (l u : Fin (m + 1))
    (ho : o ∉ boundaryClusterBlock l u) :
    BoundaryAnchoredInfinityData.closedCoordinateConditions a l u o (x.parameters l u) := by
  refine ⟨x.shape_anchor, ?_, ?_, ?_⟩
  · intro j hj
    simp [parameters, boundaryBase, hj]
  · intro j hj
    simp [parameters, boundaryVelocity, hj]
  · change x.boundaryBase l u o = _
    simp [boundaryBase, ho]

def ScaleConditions (l u : Fin (m + 1)) (x : BoundaryAnchoredInfinityFreeCoordinates a m o) : Prop :=
  ∀ j k, j < k → ¬ (j ∈ boundaryClusterBlock l u ∧ k ∈ boundaryClusterBlock l u) →
    x.radius * |x.boundaryVelocity l u k - x.boundaryVelocity l u j| <
      x.boundaryBase l u k - x.boundaryBase l u j

def OpenConditions (l u : Fin (m + 1)) (x : BoundaryAnchoredInfinityFreeCoordinates a m o) : Prop :=
  BoundaryAnchoredInfinityData.openCoordinateConditions l u o (x.parameters l u) ∧ x.ScaleConditions l u

theorem isOpen_scaleConditions (l u : Fin (m + 1)) :
    IsOpen {x : BoundaryAnchoredInfinityFreeCoordinates a m o | x.ScaleConditions l u} := by
  simp only [ScaleConditions, Set.setOf_forall]
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro k
  apply isOpen_iInter_of_finite
  intro hjk
  apply isOpen_iInter_of_finite
  intro hblock
  exact isOpen_lt (by fun_prop) (by fun_prop)

theorem isOpen_openConditions (l u : Fin (m + 1)) :
    IsOpen {x : BoundaryAnchoredInfinityFreeCoordinates a m o | x.OpenConditions l u} :=
  (BoundaryAnchoredInfinityData.isOpen_openCoordinateConditions.preimage (continuous_parameters l u)).inter
    (isOpen_scaleConditions l u)

def toDatum (x : BoundaryAnchoredInfinityFreeCoordinates a m o) (l u : Fin (m + 1))
    (hx : x.OpenConditions l u) : BoundaryAnchoredInfinityData a m l u o :=
  BoundaryAnchoredInfinityData.ofCoordinates (x.parameters l u) hx.1
    (x.closed_conditions l u hx.1.2.1)

@[simp] theorem toDatum_parameters (x : BoundaryAnchoredInfinityFreeCoordinates a m o)
    (l u : Fin (m + 1)) (hx : x.OpenConditions l u) :
    (x.toDatum l u hx).coords = x.parameters l u := BoundaryAnchoredInfinityData.coords_ofCoordinates _ _ _

def scaledInterior (x : BoundaryAnchoredInfinityFreeCoordinates a m o) (j : Fin n) : ℂ :=
  (x.radius : ℂ) * x.shape j

def scaledBoundary (l u : Fin (m + 1)) (x : BoundaryAnchoredInfinityFreeCoordinates a m o) (j : Fin m) : ℝ :=
  x.boundaryBase l u j + x.radius * x.boundaryVelocity l u j

@[fun_prop] theorem contDiff_scaledInterior (j : Fin n) :
    ContDiff ℝ ⊤ (fun x : BoundaryAnchoredInfinityFreeCoordinates a m o => x.scaledInterior j) :=
  (Complex.ofRealCLM.contDiff.comp contDiff_radius).mul (contDiff_shape j)

@[fun_prop] theorem contDiff_scaledBoundary (l u : Fin (m + 1)) (j : Fin m) :
    ContDiff ℝ ⊤ (fun x : BoundaryAnchoredInfinityFreeCoordinates a m o => x.scaledBoundary l u j) :=
  (contDiff_boundaryBase l u j).add (contDiff_radius.mul (contDiff_boundaryVelocity l u j))

def scaledCoordinates (l u : Fin (m + 1)) (x : BoundaryAnchoredInfinityFreeCoordinates a m o) :
    (Fin n → ℂ) × (Fin m → ℝ) := (x.scaledInterior, x.scaledBoundary l u)

@[fun_prop] theorem contDiff_scaledCoordinates (l u : Fin (m + 1)) :
    ContDiff ℝ ⊤ (scaledCoordinates (a := a) (o := o) l u) :=
  (contDiff_pi.mpr contDiff_scaledInterior).prodMk (contDiff_pi.mpr (contDiff_scaledBoundary l u))

end BoundaryAnchoredInfinityFreeCoordinates

def BoundaryAnchoredInfinityFreeDomain {n : ℕ} (a : Fin n) (m : ℕ)
    (l u : Fin (m + 1)) (o : Fin m) :=
  {x : BoundaryAnchoredInfinityFreeCoordinates a m o // 0 ≤ x.radius ∧ x.OpenConditions l u}

namespace BoundaryAnchoredInfinityFreeDomain

variable {n m : ℕ} {a : Fin n} {l u : Fin (m + 1)} {o : Fin m}

instance : TopologicalSpace (BoundaryAnchoredInfinityFreeDomain a m l u o) :=
  inferInstanceAs (TopologicalSpace {x : BoundaryAnchoredInfinityFreeCoordinates a m o //
    0 ≤ x.radius ∧ x.OpenConditions l u})

end BoundaryAnchoredInfinityFreeDomain

end EnvelopingIsomorphism.Deformation.Kontsevich
