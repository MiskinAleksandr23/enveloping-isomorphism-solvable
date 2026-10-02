import EnvelopingIsomorphism.Deformation.Kontsevich.GraphEdgeOrder
import EnvelopingIsomorphism.Deformation.GeneralGraphProfilePermutations
import Mathlib.GroupTheory.Perm.Fin

/-! Signs of the actual vertex-major permutations of dependent outgoing-edge blocks. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.KontsevichGraph.General

open EnvelopingIsomorphism.Deformation.Kontsevich
open scoped BigOperators Classical

theorem edgePrefix_add_le_of_lt {n : ℕ} (q : Fin n → ℕ) (v w : Fin n) (hvw : v < w) :
    edgePrefix q v + q v ≤ edgePrefix q w := by
  induction n with
  | zero => exact Fin.elim0 v
  | succ n ih =>
    cases v using Fin.cases with
    | zero =>
      cases w using Fin.cases with
      | zero => exact False.elim ((lt_irrefl _) hvw)
      | succ w => simp [edgePrefix_succ]
    | succ v =>
      cases w using Fin.cases with
      | zero => exact False.elim (not_lt_of_ge (Fin.zero_le _) hvw)
      | succ w =>
        have h := ih (fun u ↦ q u.succ) v w (Fin.succ_lt_succ_iff.mp hvw)
        simp only [edgePrefix_succ]
        omega

theorem vertexMajor_lt_of_vertex_lt {n : ℕ} (q : Fin n → ℕ) {v w : Fin n}
    (hvw : v < w) (a : Fin (q v)) (b : Fin (q w)) :
    (vertexMajorEdgeEquiv q).symm ⟨v, a⟩ < (vertexMajorEdgeEquiv q).symm ⟨w, b⟩ := by
  change ((vertexMajorEdgeEquiv q).symm ⟨v, a⟩).val < ((vertexMajorEdgeEquiv q).symm ⟨w, b⟩).val
  rw [vertexMajorEdgeEquiv_symm_val, vertexMajorEdgeEquiv_symm_val]
  have h := edgePrefix_add_le_of_lt q v w hvw
  have ha := a.isLt
  omega

theorem vertexMajor_lt_same_vertex {n : ℕ} (q : Fin n → ℕ) (v : Fin n)
    (a b : Fin (q v)) :
    (vertexMajorEdgeEquiv q).symm ⟨v, a⟩ < (vertexMajorEdgeEquiv q).symm ⟨v, b⟩ ↔ a.val < b.val := by
  change ((vertexMajorEdgeEquiv q).symm ⟨v, a⟩).val <
    ((vertexMajorEdgeEquiv q).symm ⟨v, b⟩).val ↔ _
  rw [vertexMajorEdgeEquiv_symm_val, vertexMajorEdgeEquiv_symm_val]
  exact Nat.add_lt_add_iff_left

/-- The existing canonical flattening has exactly the lexicographic vertex/slot order. -/
theorem vertexMajor_lt_iff {n : ℕ} (q : Fin n → ℕ) (e f : (v : Fin n) × Fin (q v)) :
    (vertexMajorEdgeEquiv q).symm e < (vertexMajorEdgeEquiv q).symm f ↔
      e.1 < f.1 ∨ (e.1 = f.1 ∧ e.2.val < f.2.val) := by
  rcases e with ⟨v, a⟩
  rcases f with ⟨w, b⟩
  rcases lt_trichotomy v w with hvw | rfl | hwv
  · simp only [hvw, true_or, iff_true]
    exact vertexMajor_lt_of_vertex_lt q hvw a b
  · simp only [lt_self_iff_false, true_and, false_or]
    exact vertexMajor_lt_same_vertex q v a b
  · have hnot := (vertexMajor_lt_of_vertex_lt q hwv b a).not_gt
    simp only [hnot, hwv.not_gt, hwv.ne.symm, false_and, false_or]

private theorem sign_eq_prod_all {N : ℕ} (P : Equiv.Perm (Fin N)) :
    P.sign = ∏ i, ∏ j,
      (if i < j then (if P i < P j then 1 else -1) else 1 : ℤˣ) := by
  rw [P.sign_eq_prod_prod_Ioi]
  apply Finset.prod_congr rfl
  intro i hi
  have hs : Finset.Ioi i = Finset.univ.filter (fun j : Fin N ↦ i < j) := by
    ext j
    simp
  rw [hs, Finset.prod_filter]

private theorem prod_edge_block_pairs {n : ℕ} (q : Fin n → ℕ) (F : Fin n → Fin n → ℤˣ) :
    (∏ e : (v : Fin n) × Fin (q v), ∏ f : (v : Fin n) × Fin (q v), F e.1 f.1) =
      ∏ v, ∏ w, F v w ^ (q v * q w) := by
  simp only [Fintype.prod_sigma, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  apply Finset.prod_congr rfl
  intro v hv
  rw [← Finset.prod_pow]
  simp only [← pow_mul, Nat.mul_comm]

theorem profileRowPerm_lt_iff {n : ℕ} (q : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (e f : Edge q) :
    profileRowPerm q σ ((vertexMajorEdgeEquiv q).symm e) <
        profileRowPerm q σ ((vertexMajorEdgeEquiv q).symm f) ↔
      σ e.1 < σ f.1 ∨ (e.1 = f.1 ∧ e.2.val < f.2.val) := by
  have h := vertexMajor_lt_iff (profileArity q σ) (profileEdgeEquiv q σ e) (profileEdgeEquiv q σ f)
  have hv (g : Edge q) :
      ((vertexMajorEdgeEquiv (profileArity q σ)).symm (profileEdgeEquiv q σ g)).val =
        edgePrefix (profileArity q σ) (σ g.1) + g.2.val := by
    have hflat := vertexMajorEdgeEquiv_symm_val (profileArity q σ)
      (profileEdgeEquiv q σ g).1 (profileEdgeEquiv q σ g).2
    rw [Sigma.eta] at hflat
    simpa only [profileEdgeEquiv_source, profileEdgeEquiv_slot_val] using hflat
  simpa only [Fin.lt_def, hv, profileEdgeEquiv_source,
    profileEdgeEquiv_slot_val, Equiv.apply_eq_iff_eq, profileRowPerm_edge_val] using h

private def blockSignFactor {n : ℕ} (σ : Equiv.Perm (Fin n)) (v w : Fin n) : ℤˣ :=
  if v < w then (if σ v < σ w then 1 else -1) else 1

private theorem profile_pair_factor {n : ℕ} (q : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (e f : Edge q) :
    (if (vertexMajorEdgeEquiv q).symm e < (vertexMajorEdgeEquiv q).symm f then
        (if profileRowPerm q σ ((vertexMajorEdgeEquiv q).symm e) <
            profileRowPerm q σ ((vertexMajorEdgeEquiv q).symm f) then 1 else -1) else 1 : ℤˣ) =
      blockSignFactor σ e.1 f.1 := by
  simp only [vertexMajor_lt_iff, profileRowPerm_lt_iff]
  rcases lt_trichotomy e.1 f.1 with hlt | heq | hgt
  · simp [blockSignFactor, hlt, hlt.ne]
  · simp [blockSignFactor, heq]
  · simp [blockSignFactor, hgt.not_gt, hgt.ne.symm]

private theorem blockSignFactor_pow {n : ℕ} (q : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (v w : Fin n) :
    blockSignFactor σ v w ^ (q v * q w) =
      if v < w ∧ σ w < σ v then (-1 : ℤˣ) ^ (q v * q w) else 1 := by
  by_cases hvw : v < w
  · rcases lt_trichotomy (σ v) (σ w) with hlt | heq | hgt
    · simp [blockSignFactor, hvw, hlt, hlt.not_gt]
    · exact False.elim (hvw.ne (σ.injective heq))
    · simp [blockSignFactor, hvw, hgt, hgt.not_gt]
  · simp [blockSignFactor, hvw]

/-- Exact weighted inversion formula for the genuine canonical row permutation.
All block crossings are counted, including intermediate blocks in a distant transposition. -/
theorem profileRowPerm_sign {n : ℕ} (q : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    (profileRowPerm q σ).sign =
      ∏ v, ∏ w, if v < w ∧ σ w < σ v then (-1 : ℤˣ) ^ (q v * q w) else 1 := by
  rw [sign_eq_prod_all]
  let K : Fin (∑ v, q v) → Fin (∑ v, q v) → ℤˣ := fun i j ↦
    if i < j then (if profileRowPerm q σ i < profileRowPerm q σ j then 1 else -1) else 1
  change (∏ i, ∏ j, K i j) = _
  calc
    (∏ i, ∏ j, K i j) = ∏ e : Edge q, ∏ j, K ((vertexMajorEdgeEquiv q).symm e) j :=
      (Equiv.prod_comp (vertexMajorEdgeEquiv q).symm (fun i ↦ ∏ j, K i j)).symm
    _ = ∏ e : Edge q, ∏ f : Edge q, blockSignFactor σ e.1 f.1 := by
      apply Finset.prod_congr rfl
      intro e he
      rw [← Equiv.prod_comp (vertexMajorEdgeEquiv q).symm (K ((vertexMajorEdgeEquiv q).symm e))]
      apply Finset.prod_congr rfl
      intro f hf
      exact profile_pair_factor q σ e f
    _ = ∏ v, ∏ w, blockSignFactor σ v w ^ (q v * q w) :=
      prod_edge_block_pairs q (blockSignFactor σ)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro v hv
      apply Finset.prod_congr rfl
      intro w hw
      exact blockSignFactor_pow q σ v w

/-- A pairwise even product of block lengths forces the canonical row sign to be positive. -/
theorem profileRowPerm_sign_eq_one_of_even_products {n : ℕ} (q : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (hq : ∀ v w, v ≠ w → Even (q v * q w)) :
    (profileRowPerm q σ).sign = 1 := by
  rw [profileRowPerm_sign]
  apply Finset.prod_eq_one
  intro v hv
  apply Finset.prod_eq_one
  intro w hw
  split_ifs with h
  · exact (hq v w h.1.ne).neg_one_pow
  · rfl

/-- At most one odd block is enough; the exceptional vertex may move under the permutation. -/
theorem profileRowPerm_sign_eq_one_of_at_most_one_odd {n : ℕ} (q : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (hq : ∀ v w, v ≠ w → Even (q v) ∨ Even (q w)) :
    (profileRowPerm q σ).sign = 1 := by
  apply profileRowPerm_sign_eq_one_of_even_products q σ
  intro v w hvw
  rcases hq v w hvw with hv | hw
  · exact hv.mul_right (q w)
  · exact hw.mul_left (q v)

theorem profileRowPerm_sign_eq_one_of_even {n : ℕ} (q : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (hq : ∀ v, Even (q v)) : (profileRowPerm q σ).sign = 1 :=
  profileRowPerm_sign_eq_one_of_at_most_one_odd q σ (fun v _ _ ↦ Or.inl (hq v))

theorem profileRowPerm_sign_eq_one_of_even_off {n : ℕ} (q : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (i : Fin n) (hq : ∀ v, v ≠ i → Even (q v)) :
    (profileRowPerm q σ).sign = 1 := by
  apply profileRowPerm_sign_eq_one_of_at_most_one_odd q σ
  intro v w hvw
  by_cases hvi : v = i
  · exact Or.inr (hq w (fun hwi ↦ hvw (hvi.trans hwi.symm)))
  · exact Or.inl (hq v hvi)

theorem profileRowPerm_sign_binary {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (profileRowPerm (fun _ ↦ 2) σ).sign = 1 :=
  profileRowPerm_sign_eq_one_of_even _ σ (fun _ ↦ by decide)

/-- In particular a single vector or trivector vertex among bivector vertices contributes
no internal block-permutation sign. This holds for any exceptional arity. -/
theorem profileRowPerm_sign_single_exception {n : ℕ} (σ : Equiv.Perm (Fin n))
    (i : Fin n) (a : ℕ) : (profileRowPerm (fun v ↦ if v = i then a else 2) σ).sign = 1 := by
  apply profileRowPerm_sign_eq_one_of_even_off _ σ i
  intro v hv
  simp [hv]

theorem profileRowPerm_symm_sign_eq_one_of_even_off {n : ℕ} (q : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (i : Fin n) (hq : ∀ v, v ≠ i → Even (q v)) :
    Equiv.Perm.sign (profileRowPerm q σ).symm = 1 := by
  change ((profileRowPerm q σ)⁻¹).sign = 1
  rw [Equiv.Perm.sign_inv, profileRowPerm_sign_eq_one_of_even_off q σ i hq]

end EnvelopingIsomorphism.Deformation.KontsevichGraph.General
