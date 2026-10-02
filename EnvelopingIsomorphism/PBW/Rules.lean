import EnvelopingIsomorphism.PBW.Reduction
import EnvelopingIsomorphism.PBW.Words
import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.Finsupp.Defs

/-! The monic quadratic-linear rules attached to a basis of a Lie algebra. -/

noncomputable section

namespace EnvelopingIsomorphism.PBW

open Finsupp

variable {R L α : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
variable [LinearOrder α] (b : Module.Basis α R L)

/-- Insert a Lie vector into a word context, using its basis coefficients. -/
def insert (p s : List α) : L →ₗ[R] (List α →₀ R) :=
  (Finsupp.lmapDomain R R (fun k ↦ p ++ k :: s)).comp b.repr.toLinearMap

@[simp] theorem insert_basis (p s : List α) (i : α) :
    insert b p s (b i) = single (p ++ i :: s) 1 := by
  simp [insert]

theorem insert_support {p s v : List α} {x : L}
    (hv : v ∈ (insert b p s x).support) : ∃ k, v = p ++ k :: s := by
  classical
  have h := Finsupp.mapDomain_support hv
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
  exact ⟨k, hk.symm⟩

theorem insert_support_coeff {p s v : List α} {x : L}
    (hv : v ∈ (insert b p s x).support) :
    ∃ k, b.repr x k ≠ 0 ∧ v = p ++ k :: s := by
  classical
  have h := Finsupp.mapDomain_support hv
  obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp h
  exact ⟨k, Finsupp.mem_support_iff.mp hk, heq.symm⟩

/-- The right hand side of an adjacent PBW swap. -/
def rhs (p : List α) (i j : α) (s : List α) : List α →₀ R :=
  single (p ++ j :: i :: s) 1 + insert b p s ⁅b i, b j⁆

/-- The contextual defining relation, including pairs in either order. -/
def relation (p : List α) (i j : α) (s : List α) : List α →₀ R :=
  single (p ++ i :: j :: s) 1 - rhs b p i j s

@[simp] theorem relation_self (p s : List α) (i : α) : relation b p i i s = 0 := by
  simp [relation, rhs]

theorem relation_swap (p s : List α) (i j : α) :
    relation b p i j s = -relation b p j i s := by
  rw [relation, relation, rhs, rhs, ← lie_skew (b i) (b j), map_neg]
  abel

/-- One monic reduction at an arbitrary adjacent strict inversion. -/
def Step (w : List α) (q : List α →₀ R) : Prop :=
  ∃ p i j s, j < i ∧ w = p ++ i :: j :: s ∧ q = rhs b p i j s

theorem step_support_smaller {w : List α} {q : List α →₀ R}
    (hq : Step b w q) {v : List α} (hv : v ∈ q.support) : WordLT v w := by
  classical
  obtain ⟨p, i, j, s, hji, rfl, rfl⟩ := hq
  rcases Finset.mem_union.mp (Finsupp.support_add hv) with hv | hv
  · have heq : v = p ++ j :: i :: s := by
      exact Finset.mem_singleton.mp (Finsupp.support_single_subset hv)
    rw [heq]
    exact wordLT_swap p s hji
  · obtain ⟨k, rfl⟩ := insert_support b hv
    exact wordLT_replacePair p s i j k

/-- PBW as a terminating monic linear rewrite system. -/
def reductionSystem : ReductionSystem R (List α) where
  smaller := WordLT
  wellFounded := wordLT_wellFounded
  step := Step b
  support_smaller h v hv := step_support_smaller b h hv

theorem normal_iff_pairwise (w : List α) :
    (reductionSystem b).Normal w ↔ w.Pairwise (· ≤ ·) := by
  rw [pairwise_iff_no_adjacent_inversion]
  simp only [ReductionSystem.Normal, reductionSystem, Step]
  constructor
  · intro h ⟨p, i, j, s, hw, hij⟩
    exact h ⟨rhs b p i j s, p, i, j, s, hij, hw, rfl⟩
  · intro h ⟨q, p, i, j, s, hij, hw, _⟩
    exact h ⟨p, i, j, s, hw, hij⟩

theorem relation_mem_lower_of_lt (p s : List α) (i j : α) (w : List α)
    (hji : j < i) (h : WordLT (p ++ i :: j :: s) w) :
    relation b p i j s ∈ (reductionSystem b).lowerRelations w :=
  Submodule.subset_span ⟨p ++ i :: j :: s, rhs b p i j s, h,
    ⟨p, i, j, s, hji, rfl, rfl⟩, rfl⟩

/-- Every strictly shorter contextual relation may be used, regardless of its orientation. -/
theorem relation_mem_lower_of_length_lt (p s : List α) (i j : α) (w : List α)
    (h : (p ++ i :: j :: s).length < w.length) :
    relation b p i j s ∈ (reductionSystem b).lowerRelations w := by
  rcases lt_trichotomy j i with hij | rfl | hij
  · exact relation_mem_lower_of_lt b p s i j w hij (wordLT_of_length_lt h)
  · simp
  · rw [relation_swap]
    apply Submodule.neg_mem
    apply relation_mem_lower_of_lt b p s j i w hij
    apply wordLT_of_length_lt
    simpa using h

end EnvelopingIsomorphism.PBW
