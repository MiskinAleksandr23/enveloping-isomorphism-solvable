import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic

/-! Canonical vertex-major order on dependent finite outgoing-edge sets. -/

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open scoped BigOperators

/-- The explicit empty edge equivalence. -/
def emptyEdgeEquiv (q : Fin 0 → ℕ) : Fin 0 ≃ ((v : Fin 0) × Fin (q v)) where
  toFun := Fin.elim0
  invFun e := Fin.elim0 e.1
  left_inv x := Fin.elim0 x
  right_inv e := Fin.elim0 e.1

/-- Split the first vertex's ordered edges from all remaining vertices. -/
def edgeHeadTailEquiv {n : ℕ} (q : Fin (n + 1) → ℕ) :
    (Fin (q 0) ⊕ ((v : Fin n) × Fin (q v.succ))) ≃ ((v : Fin (n + 1)) × Fin (q v)) where
  toFun
    | .inl a => ⟨0, a⟩
    | .inr ⟨v, a⟩ => ⟨v.succ, a⟩
  invFun e := Fin.cases (fun a ↦ Sum.inl a) (fun v a ↦ Sum.inr ⟨v, a⟩) e.1 e.2
  left_inv e := by cases e with | inl a => rfl | inr e => cases e; rfl
  right_inv e := by
    rcases e with ⟨v, a⟩
    cases v using Fin.cases <;> rfl

/-- List all outgoing slots vertex by vertex, in the natural order of each `Fin` fiber.
The construction uses only explicit head/tail splitting, never an arbitrary finite enumeration. -/
def vertexMajorEdgeEquiv : {n : ℕ} → (q : Fin n → ℕ) →
    Fin (∑ v, q v) ≃ ((v : Fin n) × Fin (q v))
  | 0, q => (finCongr (by simp)).trans (emptyEdgeEquiv q)
  | n + 1, q =>
      (finCongr (Fin.sum_univ_succ q)).trans
        (finSumFinEquiv.symm.trans
          ((Equiv.sumCongr (Equiv.refl _) (vertexMajorEdgeEquiv (fun v : Fin n ↦ q v.succ))).trans
            (edgeHeadTailEquiv q)))

/-- Number of outgoing edges at vertices strictly preceding `v`. -/
def edgePrefix {n : ℕ} (q : Fin n → ℕ) (v : Fin n) : ℕ :=
  ∑ u : Fin n, if u < v then q u else 0

@[simp] theorem edgePrefix_zero {n : ℕ} (q : Fin (n + 1) → ℕ) : edgePrefix q 0 = 0 := by
  simp [edgePrefix]

theorem edgePrefix_succ {n : ℕ} (q : Fin (n + 1) → ℕ) (v : Fin n) :
    edgePrefix q v.succ = q 0 + edgePrefix (fun u : Fin n ↦ q u.succ) v := by
  simp [edgePrefix, Fin.sum_univ_succ]

@[simp] theorem vertexMajorEdgeEquiv_symm_zero_val {n : ℕ} (q : Fin (n + 1) → ℕ)
    (a : Fin (q 0)) : ((vertexMajorEdgeEquiv q).symm ⟨0, a⟩).val = a.val := rfl

@[simp] theorem vertexMajorEdgeEquiv_symm_succ_val {n : ℕ} (q : Fin (n + 1) → ℕ)
    (v : Fin n) (a : Fin (q v.succ)) :
    ((vertexMajorEdgeEquiv q).symm ⟨v.succ, a⟩).val =
      q 0 + ((vertexMajorEdgeEquiv (fun u : Fin n ↦ q u.succ)).symm ⟨v, a⟩).val := rfl

/-- The flattening formula certifies the vertex-major order independently of the construction. -/
theorem vertexMajorEdgeEquiv_symm_val {n : ℕ} (q : Fin n → ℕ) (v : Fin n) (a : Fin (q v)) :
    ((vertexMajorEdgeEquiv q).symm ⟨v, a⟩).val = edgePrefix q v + a.val := by
  induction n with
  | zero => exact Fin.elim0 v
  | succ n ih =>
    cases v using Fin.cases with
    | zero => simp
    | succ v =>
      rw [vertexMajorEdgeEquiv_symm_succ_val, edgePrefix_succ, ih]
      omega

/-- For one vertex the cardinality cast is the only change in the slot index. -/
def oneVertexEdgeDomainEquiv (q : Fin 1 → ℕ) : Fin (∑ v, q v) ≃ Fin (q 0) :=
  finCongr (Fin.sum_univ_one q)

theorem vertexMajorEdgeEquiv_one (q : Fin 1 → ℕ) (a : Fin (q 0)) :
    vertexMajorEdgeEquiv q ((oneVertexEdgeDomainEquiv q).symm a) = ⟨0, a⟩ := by
  apply (vertexMajorEdgeEquiv q).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Fin.ext
  rw [vertexMajorEdgeEquiv_symm_zero_val]
  rfl

theorem edgePrefix_constant {n : ℕ} (k : ℕ) (v : Fin n) :
    edgePrefix (fun _ : Fin n ↦ k) v = k * v.val := by
  induction n with
  | zero => exact Fin.elim0 v
  | succ n ih =>
    cases v using Fin.cases with
    | zero => simp
    | succ v =>
      rw [edgePrefix_succ, ih]
      simp [Nat.mul_add, Nat.add_comm]

/-- The explicit cardinality identification for a constant outgoing arity. -/
def constantEdgeDomainEquiv (n k : ℕ) : Fin (∑ _ : Fin n, k) ≃ Fin (n * k) :=
  finCongr (by simp)

/-- Constant arity recovers the native row-major product index `(vertex, slot)`. -/
theorem vertexMajorEdgeEquiv_constant_symm {n : ℕ} (k : ℕ) (v : Fin n) (a : Fin k) :
    (vertexMajorEdgeEquiv (fun _ : Fin n ↦ k)).symm ⟨v, a⟩ =
      (constantEdgeDomainEquiv n k).symm (finProdFinEquiv (v, a)) := by
  apply Fin.ext
  rw [vertexMajorEdgeEquiv_symm_val, edgePrefix_constant]
  change k * v.val + a.val = a.val + k * v.val
  exact Nat.add_comm _ _

theorem vertexMajorEdgeEquiv_constant {n : ℕ} (k : ℕ) (e : Fin (n * k)) :
    vertexMajorEdgeEquiv (fun _ : Fin n ↦ k) ((constantEdgeDomainEquiv n k).symm e) =
      ⟨(finProdFinEquiv.symm e).1, (finProdFinEquiv.symm e).2⟩ := by
  apply (vertexMajorEdgeEquiv (fun _ : Fin n ↦ k)).symm.injective
  rw [Equiv.symm_apply_apply, vertexMajorEdgeEquiv_constant_symm]
  congr 1
  exact (Equiv.apply_symm_apply finProdFinEquiv e).symm

/-- In particular, the legacy bivector edge order is slot plus twice the vertex. -/
theorem vertexMajorEdgeEquiv_two_symm_val {n : ℕ} (v : Fin n) (a : Fin 2) :
    ((vertexMajorEdgeEquiv (fun _ : Fin n ↦ 2)).symm ⟨v, a⟩).val = a.val + 2 * v.val := by
  rw [vertexMajorEdgeEquiv_symm_val, edgePrefix_constant, Nat.add_comm]

end EnvelopingIsomorphism.Deformation.Kontsevich
