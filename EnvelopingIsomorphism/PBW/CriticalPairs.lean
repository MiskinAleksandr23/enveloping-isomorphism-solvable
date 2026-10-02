import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.FreeAlgebra
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Tactic.NoncommRing
import EnvelopingIsomorphism.PBW.Rules

/-!
# The Jacobi identity resolving the PBW triple overlap

For any linear map from a Lie algebra into an associative algebra, the two
first rewrites of a three-letter word differ by four contextual relations on
permuted words and three relations of length two. The nested Lie terms cancel
by Jacobi. The identities below do not assume the map preserves brackets.
-/

noncomputable section

namespace EnvelopingIsomorphism.PBW

variable {R L A : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [Ring A] [Algebra R A]

/-- The defining enveloping-algebra relation measured along a linear map. -/
def lieRelation (f : L →ₗ[R] A) (x y : L) : A :=
  f x * f y - f y * f x - f ⁅x, y⁆

@[simp] theorem lieRelation_self (f : L →ₗ[R] A) (x : L) :
    lieRelation f x x = 0 := by simp [lieRelation]

theorem lieRelation_swap (f : L →ₗ[R] A) (x y : L) :
    lieRelation f y x = -lieRelation f x y := by
  simp only [lieRelation]
  rw [← lie_skew x y, map_neg]
  noncomm_ring

theorem lieRelation_add_left (f : L →ₗ[R] A) (x y z : L) :
    lieRelation f (x + y) z = lieRelation f x z + lieRelation f y z := by
  simp only [lieRelation, add_lie, map_add]
  noncomm_ring

theorem lieRelation_add_right (f : L →ₗ[R] A) (x y z : L) :
    lieRelation f x (y + z) = lieRelation f x y + lieRelation f x z := by
  simp only [lieRelation, lie_add, map_add]
  noncomm_ring

theorem lieRelation_smul_left (f : L →ₗ[R] A) (a : R) (x y : L) :
    lieRelation f (a • x) y = a • lieRelation f x y := by
  simp [lieRelation, smul_lie, smul_sub]

theorem lieRelation_smul_right (f : L →ₗ[R] A) (a : R) (x y : L) :
    lieRelation f x (a • y) = a • lieRelation f x y := by
  simp [lieRelation, lie_smul, smul_sub]

/-- After swapping all three inverted pairs, the remaining ambiguity has
length two. Its apparent degree-one remainder is exactly Jacobi. -/
theorem swapped_triple_overlap_identity (f : L →ₗ[R] A) (x y z : L) :
    (f ⁅y, z⁆ * f x + f y * f ⁅x, z⁆ + f ⁅x, y⁆ * f z) -
      (f z * f ⁅x, y⁆ + f ⁅x, z⁆ * f y + f x * f ⁅y, z⁆) =
    lieRelation f ⁅x, y⁆ z + lieRelation f y ⁅x, z⁆ -
      lieRelation f x ⁅y, z⁆ := by
  simp only [lieRelation, lie_lie, map_sub]
  noncomm_ring

/-- The difference between reducing the left or right pair of a three-letter
word is an explicit sum of contextual relations. -/
theorem triple_overlap_identity (f : L →ₗ[R] A) (x y z : L) :
    (f y * f x * f z + f ⁅x, y⁆ * f z) -
      (f x * f z * f y + f x * f ⁅y, z⁆) =
    lieRelation f y z * f x + f y * lieRelation f x z -
      f z * lieRelation f x y - lieRelation f x z * f y +
      lieRelation f ⁅x, y⁆ z + lieRelation f y ⁅x, z⁆ -
      lieRelation f x ⁅y, z⁆ := by
  simp only [lieRelation, lie_lie, map_sub]
  noncomm_ring

/-- The triple-overlap identity is valid inside arbitrary left and right
contexts. No commutativity of the target algebra is used. -/
theorem triple_overlap_context_identity (f : L →ₗ[R] A) (a c : A) (x y z : L) :
    a * (f y * f x * f z + f ⁅x, y⁆ * f z) * c -
      a * (f x * f z * f y + f x * f ⁅y, z⁆) * c =
    a * (lieRelation f y z * f x) * c +
      a * (f y * lieRelation f x z) * c -
      a * (f z * lieRelation f x y) * c -
      a * (lieRelation f x z * f y) * c +
      a * lieRelation f ⁅x, y⁆ z * c +
      a * lieRelation f y ⁅x, z⁆ * c -
      a * lieRelation f x ⁅y, z⁆ * c := by
  calc
    _ = a * ((f y * f x * f z + f ⁅x, y⁆ * f z) -
        (f x * f z * f y + f x * f ⁅y, z⁆)) * c := by noncomm_ring
    _ = _ := by rw [triple_overlap_identity]; noncomm_ring

/-- Standard realization in Mathlib's free algebra on a chosen basis. -/
def basisFreeLinear {α : Type*} (b : Module.Basis α R L) :
    L →ₗ[R] FreeAlgebra R α :=
  b.constr R (FreeAlgebra.ι R)

@[simp] theorem basisFreeLinear_basis {α : Type*} (b : Module.Basis α R L) (i : α) :
    basisFreeLinear b (b i) = FreeAlgebra.ι R i := by
  simp [basisFreeLinear]

section WordRelations

variable {α : Type*} [LinearOrder α] (b : Module.Basis α R L)

/-- Bilinear insertion of two Lie vectors into a word context. -/
def pairInsert (p s : List α) : L →ₗ[R] L →ₗ[R] (List α →₀ R) :=
  b.constr R (fun i ↦ insert b (p ++ [i]) s)

omit [LinearOrder α] in
@[simp] theorem pairInsert_basis_left (p s : List α) (i : α) (y : L) :
    pairInsert b p s (b i) y = insert b (p ++ [i]) s y := by
  simp [pairInsert]

@[simp] theorem pairInsert_basis_right (p s : List α) (x : L) (i : α) :
    pairInsert b p s x (b i) = insert b p (i :: s) x := by
  have h : (pairInsert b p s).flip (b i) = insert b p (i :: s) := by
    apply b.ext
    intro j
    simp [LinearMap.flip_apply, List.append_assoc]
  exact LinearMap.congr_fun h x

/-- The contextual Lie relation, extended bilinearly from basis pairs. -/
def pairRelation (p s : List α) : L →ₗ[R] L →ₗ[R] (List α →₀ R) where
  toFun x :=
    { toFun y := pairInsert b p s x y - pairInsert b p s y x - insert b p s ⁅x, y⁆
      map_add' y z := by
        simp only [map_add, LinearMap.add_apply, lie_add]
        abel
      map_smul' a y := by
        simp [lie_smul, smul_sub] }
  map_add' x y := by
    ext z
    simp only [LinearMap.coe_mk, AddHom.coe_mk, map_add, LinearMap.add_apply, add_lie]
    abel
  map_smul' a x := by
    ext y
    simp [smul_lie, smul_sub]

omit [LinearOrder α] in
theorem pairRelation_apply (p s : List α) (x y : L) :
    pairRelation b p s x y =
      pairInsert b p s x y - pairInsert b p s y x - insert b p s ⁅x, y⁆ := rfl

@[simp] theorem pairRelation_basis (p s : List α) (i j : α) :
    pairRelation b p s (b i) (b j) = relation b p i j s := by
  simp [pairRelation_apply, relation, rhs]
  abel

/-- Exact resolution of the contextual three-letter critical pair. The first
four summands have permuted leading words; the final three have length two. -/
theorem rhs_triple_overlap_identity (p s : List α) (k j i : α) :
    rhs b p k j (i :: s) - rhs b (p ++ [k]) j i s =
      relation b p j i (k :: s) + relation b (p ++ [j]) k i s -
        relation b (p ++ [i]) k j s - relation b p k i (j :: s) +
        pairRelation b p s ⁅b k, b j⁆ (b i) +
        pairRelation b p s (b j) ⁅b k, b i⁆ -
        pairRelation b p s (b k) ⁅b j, b i⁆ := by
  simp only [pairRelation_apply, pairInsert_basis_left, pairInsert_basis_right,
    relation, rhs, List.append_assoc, List.singleton_append, lie_lie, map_sub]
  abel

omit [LinearOrder α] in
private theorem linear_mem_of_basis {V : Type*} [AddCommGroup V] [Module R V]
    (S : Submodule R V) (f : L →ₗ[R] V) (h : ∀ i, f (b i) ∈ S) (x : L) :
    f x ∈ S := by
  have hspan : Submodule.span R (Set.range b) ≤ S.comap f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact h i
  rw [b.span_eq] at hspan
  exact hspan (Submodule.mem_top : x ∈ (⊤ : Submodule R L))

/-- Short relations with arbitrary Lie-vector inputs follow by bilinearity
from the corresponding basis relations. -/
theorem pairRelation_mem_lower_of_length_lt (p s w : List α) (x y : L)
    (hlen : p.length + 2 + s.length < w.length) :
    pairRelation b p s x y ∈ (reductionSystem b).lowerRelations w := by
  apply linear_mem_of_basis b _ ((pairRelation b p s).flip y)
  intro i
  apply linear_mem_of_basis b _ (pairRelation b p s (b i))
  intro j
  simp only [pairRelation_basis]
  apply relation_mem_lower_of_length_lt
  simp only [List.length_append, List.length_cons]
  omega

/-- The only overlapping PBW critical pair is resolved by relations with a
strictly smaller leading word. -/
theorem triple_mem_lower (p s : List α) (k j i : α) (hjk : j < k) (hij : i < j) :
    rhs b p k j (i :: s) - rhs b (p ++ [k]) j i s ∈
      (reductionSystem b).lowerRelations (p ++ k :: j :: i :: s) := by
  let S := (reductionSystem b).lowerRelations (p ++ k :: j :: i :: s)
  have hik : i < k := hij.trans hjk
  have h₁ : relation b p j i (k :: s) ∈ S := by
    apply relation_mem_lower_of_lt b p (k :: s) j i _ hij
    apply wordLT_of_length_eq_of_inversionCount_lt
    · simp
    · have hleft := inversionCount_swap p (i :: s) hjk
      have hnext := inversionCount_swap (p ++ [j]) s hik
      simp only [List.append_assoc, List.singleton_append] at hnext
      omega
  have h₂ : relation b (p ++ [j]) k i s ∈ S := by
    apply relation_mem_lower_of_lt b (p ++ [j]) s k i _ hik
    simpa only [List.append_assoc, List.singleton_append] using wordLT_swap p (i :: s) hjk
  have h₃ : relation b (p ++ [i]) k j s ∈ S := by
    apply relation_mem_lower_of_lt b (p ++ [i]) s k j _ hjk
    apply wordLT_of_length_eq_of_inversionCount_lt
    · simp
    · have hright := inversionCount_swap (p ++ [k]) s hij
      have hnext := inversionCount_swap p (j :: s) hik
      simp only [List.append_assoc, List.singleton_append] at hright ⊢
      omega
  have h₄ : relation b p k i (j :: s) ∈ S := by
    apply relation_mem_lower_of_lt b p (j :: s) k i _ hik
    simpa only [List.append_assoc, List.singleton_append] using
      wordLT_swap (p ++ [k]) s hij
  have hshort (x y : L) : pairRelation b p s x y ∈ S := by
    apply pairRelation_mem_lower_of_length_lt
    simp only [List.length_append, List.length_cons]
    omega
  rw [rhs_triple_overlap_identity]
  exact S.sub_mem
    (S.add_mem
      (S.add_mem (S.sub_mem (S.sub_mem (S.add_mem h₁ h₂) h₃) h₄)
        (hshort ⁅b k, b j⁆ (b i)))
      (hshort (b j) ⁅b k, b i⁆))
    (hshort (b k) ⁅b j, b i⁆)

end WordRelations

end EnvelopingIsomorphism.PBW
