import EnvelopingIsomorphism.Deformation.GraphDegree
import Mathlib.Logic.Equiv.Fin.Basic

/-! Position-labelled Leibniz expansion for the actual iterated graph derivatives. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation

open MvPolynomial
open scoped BigOperators

section FirstOrder

variable {R A J : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq J]

/-- The first-order product rule as a sum of products with exactly one differentiated factor. -/
theorem derivation_prod_update (D : Derivation R A A) (s : Finset J) (f : J → A) :
    D (∏ j ∈ s, f j) = ∑ j ∈ s, ∏ k ∈ s, Function.update f j (D (f j)) k := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, D.leibniz, ih, Finset.sum_insert hj]
    have hself : (∏ k ∈ insert j s, Function.update f j (D (f j)) k) =
        D (f j) * ∏ k ∈ s, f k := by
      rw [Finset.prod_insert hj, Function.update_self, Finset.prod_update_of_notMem hj]
    have hother : (∑ k ∈ s, ∏ l ∈ insert j s, Function.update f k (D (f k)) l) =
        f j * ∑ k ∈ s, ∏ l ∈ s, Function.update f k (D (f k)) l := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hjk : j ≠ k := fun h ↦ hj (h.symm ▸ hk)
      rw [Finset.prod_insert hj, Function.update_of_ne hjk]
    rw [hself, hother]
    simp only [smul_eq_mul]
    ring

theorem derivation_fintype_prod_update [Fintype J] (D : Derivation R A A) (f : J → A) :
    D (∏ j, f j) = ∑ j, ∏ k, Function.update f j (D (f j)) k :=
  derivation_prod_update D Finset.univ f

end FirstOrder

section Assignments

variable {σ J : Type*} [DecidableEq J]

/-- The ordered subsequence of derivative indices assigned to a factor. Assignments are
indexed by positions in the original list, so repeated derivative indices remain distinct. -/
def assignedDerivatives : (ds : List σ) → (Fin ds.length → J) → J → List σ
  | [], _, _ => []
  | i :: ds, a, j =>
      if a 0 = j then i :: assignedDerivatives ds (fun p ↦ a p.succ) j
      else assignedDerivatives ds (fun p ↦ a p.succ) j

@[simp] theorem assignedDerivatives_nil (a : Fin 0 → J) (j : J) :
    assignedDerivatives ([] : List σ) a j = [] := rfl

/-- Separate the head derivative's factor choice from all remaining position choices. -/
def derivativeAssignmentEquiv (n : ℕ) : (Fin (n + 1) → J) ≃ J × (Fin n → J) where
  toFun a := (a 0, fun p ↦ a p.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv a := by
    funext i
    refine Fin.cases rfl (fun _ ↦ rfl) i
  right_inv p := by cases p; rfl

theorem sum_length_assignedDerivatives [Fintype J] (ds : List σ) (a : Fin ds.length → J) :
    ∑ j, (assignedDerivatives ds a j).length = ds.length := by
  induction ds with
  | nil => simp
  | cons i ds ih =>
    have hlen (j : J) : (assignedDerivatives (i :: ds) a j).length =
        (assignedDerivatives ds (fun p ↦ a p.succ) j).length + if a 0 = j then 1 else 0 := by
      simp only [assignedDerivatives]
      split_ifs <;> simp
    simp_rw [hlen]
    rw [Finset.sum_add_distrib, ih]
    simp

end Assignments

section Iterated

variable {R σ J : Type*} [CommRing R] [DecidableEq J] [Fintype J]

omit [Fintype J] in
theorem assignedDerivatives_cons_factor (i : σ) (ds : List σ) (a : Fin (ds.length + 1) → J)
    (f : J → MvPolynomial σ R) (j : J) :
    iteratedPDeriv (assignedDerivatives (i :: ds) a j) (f j) =
      Function.update
        (fun k ↦ iteratedPDeriv (assignedDerivatives ds (fun p ↦ a p.succ) k) (f k))
        (a 0) (pderiv i (iteratedPDeriv (assignedDerivatives ds (fun p ↦ a p.succ) (a 0)) (f (a 0)))) j := by
  by_cases hj : j = a 0
  · subst j
    simp [assignedDerivatives]
  · simp [assignedDerivatives, hj, Ne.symm hj]

/-- Exact iterated Leibniz expansion. Each derivative POSITION independently chooses one
factor, and the order of indices assigned to each factor is retained. -/
theorem iteratedPDeriv_fintype_prod (ds : List σ) (f : J → MvPolynomial σ R) :
    iteratedPDeriv ds (∏ j, f j) =
      ∑ a : Fin ds.length → J, ∏ j, iteratedPDeriv (assignedDerivatives ds a j) (f j) := by
  induction ds with
  | nil => simp [assignedDerivatives]
  | cons i ds ih =>
    rw [iteratedPDeriv_cons, ih, map_sum]
    simp_rw [derivation_fintype_prod_update]
    rw [Finset.sum_comm]
    let F : J × (Fin ds.length → J) → MvPolynomial σ R := fun p ↦
      ∏ k, Function.update
        (fun j ↦ iteratedPDeriv (assignedDerivatives ds p.2 j) (f j)) p.1
        (pderiv i (iteratedPDeriv (assignedDerivatives ds p.2 p.1) (f p.1))) k
    change (∑ j, ∑ a, F (j, a)) = _
    rw [← Fintype.sum_prod_type F]
    symm
    apply Fintype.sum_equiv (derivativeAssignmentEquiv ds.length)
    intro a
    apply Finset.prod_congr rfl
    intro j hj
    exact assignedDerivatives_cons_factor i ds a f j

omit [Fintype J] in
/-- A finite subfamily version, allowing the factor index type itself to be infinite. -/
theorem iteratedPDeriv_finset_prod (ds : List σ) (s : Finset J) (f : J → MvPolynomial σ R) :
    iteratedPDeriv ds (∏ j ∈ s, f j) =
      ∑ a : Fin ds.length → s, ∏ j : s,
        iteratedPDeriv (assignedDerivatives ds a j) (f j) := by
  simpa only [Finset.prod_coe_sort] using
    iteratedPDeriv_fintype_prod ds (fun j : s ↦ f j)

/-- A positive number of derivative positions cannot be assigned to an empty factor family. -/
theorem iteratedPDeriv_fintype_prod_of_isEmpty [IsEmpty J] (ds : List σ) (hds : ds ≠ [])
    (f : J → MvPolynomial σ R) : iteratedPDeriv ds (∏ j, f j) = 0 := by
  cases ds with
  | nil => exact (hds rfl).elim
  | cons i ds =>
    rw [iteratedPDeriv_fintype_prod]
    haveI : IsEmpty (Fin (i :: ds).length → J) := ⟨fun a ↦ isEmptyElim (a 0)⟩
    simp

/-- Repeated coordinate indices retain the expected multiplicity of the two mixed assignments. -/
theorem iteratedPDeriv_two_equal_mul (i : σ) (f g : MvPolynomial σ R) :
    iteratedPDeriv [i, i] (f * g) =
      iteratedPDeriv [i, i] f * g + 2 • (pderiv i f * pderiv i g) +
        f * iteratedPDeriv [i, i] g := by
  simp only [iteratedPDeriv_cons, iteratedPDeriv_nil, pderiv_mul, map_add, two_smul]
  ring

end Iterated

end EnvelopingIsomorphism.Deformation
