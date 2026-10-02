import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Projection
import Mathlib.Logic.Equiv.Fin.Basic

/-! A finite terminating filtration of vector spaces admits an adapted weighted basis. -/

noncomputable section

namespace EnvelopingIsomorphism.LinearAlgebra

open Module

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

def complementBasis {α β : Type*} (P Q : Submodule k V) (h : IsCompl P Q)
    (bP : Basis α k P) (bQ : Basis β k Q) : Basis (α ⊕ β) k V :=
  (bP.prod bQ).map (P.prodEquivOfIsCompl Q h)

@[simp] theorem complementBasis_inl {α β : Type*} (P Q : Submodule k V) (h : IsCompl P Q)
    (bP : Basis α k P) (bQ : Basis β k Q) (i : α) :
    complementBasis P Q h bP bQ (Sum.inl i) = (bP i : V) := by
  simp [complementBasis, Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']

@[simp] theorem complementBasis_inr {α β : Type*} (P Q : Submodule k V) (h : IsCompl P Q)
    (bP : Basis α k P) (bQ : Basis β k Q) (i : β) :
    complementBasis P Q h bP bQ (Sum.inr i) = (bQ i : V) := by
  simp [complementBasis, Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']

theorem span_complementBasis_weight_succ {α β : Type*}
    (P Q : Submodule k V) (h : IsCompl P Q) (bP : Basis α k P) (bQ : Basis β k Q)
    (ω : α → ℕ) (d : ℕ) :
    Submodule.span k (complementBasis P Q h bP bQ ''
      {i | d + 1 ≤ Sum.elim (fun a ↦ ω a + 1) (fun _ ↦ 0) i}) =
    (Submodule.span k (bP '' {i | d ≤ ω i})).map P.subtype := by
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    cases i with
    | inl i =>
      refine ⟨bP i, ⟨i, ?_, rfl⟩, ?_⟩
      · exact Nat.succ_le_succ_iff.mp hi
      · simp
    | inr i => exact (Nat.not_succ_le_zero d hi).elim
  · rintro ⟨x, ⟨i, hi, rfl⟩, rfl⟩
    refine ⟨Sum.inl i, ?_, ?_⟩
    · exact Nat.succ_le_succ hi
    · simp

theorem span_reindex_weight {α β : Type*} (b : Basis α k V)
    (e : α ≃ β) (ω : α → ℕ) (d : ℕ) :
    Submodule.span k (b.reindex e '' {j | d ≤ ω (e.symm j)}) =
      Submodule.span k (b '' {i | d ≤ ω i}) := by
  congr 1
  ext x
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨e.symm j, hj, by simp⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨e i, by simpa using hi, by simp⟩

/-- A finite descending filtration has a basis whose nonnegative weights recover every layer.
The first piece is the entire space; the final zero piece bounds all basis weights. -/
theorem exists_adapted_weighted_basis [Module.Finite k V]
    (F : ℕ → Submodule k V) (hzero : F 0 = ⊤) (hmono : Antitone F)
    (c : ℕ) (hterm : F (c + 1) = ⊥) :
    ∃ n : ℕ, ∃ b : Basis (Fin n) k V, ∃ ω : Fin n → ℕ,
      (∀ i, ω i ≤ c) ∧ ∀ d, Submodule.span k (b '' {i | d ≤ ω i}) = F d := by
  classical
  induction c generalizing V with
  | zero =>
    refine ⟨Module.finrank k V, Module.finBasis k V, fun _ ↦ 0, fun _ ↦ le_rfl, ?_⟩
    intro d
    cases d with
    | zero => simpa [hzero] using (Module.finBasis k V).span_eq
    | succ d =>
      have hFd : F (d + 1) = ⊥ := le_bot_iff.mp ((hmono (Nat.succ_le_succ (Nat.zero_le d))).trans_eq hterm)
      simp [hFd]
  | succ c ih =>
    let P := F 1
    let G : ℕ → Submodule k P := fun d ↦ (F (d + 1)).comap P.subtype
    have hG0 : G 0 = ⊤ := Submodule.comap_subtype_self P
    have hGmono : Antitone G := fun i j hij ↦ Submodule.comap_mono (hmono (Nat.add_le_add_right hij 1))
    have hGterm : G (c + 1) = ⊥ := by
      change (F (c + 1 + 1)).comap P.subtype = ⊥
      rw [hterm]
      simp
    obtain ⟨nP, bP, ωP, hωP, hbP⟩ := ih G hG0 hGmono hGterm
    obtain ⟨Q, hPQ⟩ := P.exists_isCompl
    let bQ := Module.finBasis k Q
    let B := complementBasis P Q hPQ bP bQ
    let ωB : Fin nP ⊕ Fin (Module.finrank k Q) → ℕ :=
      Sum.elim (fun i ↦ ωP i + 1) (fun _ ↦ 0)
    refine ⟨nP + Module.finrank k Q, B.reindex finSumFinEquiv,
      fun i ↦ ωB (finSumFinEquiv.symm i), ?_, ?_⟩
    · intro i
      cases h : finSumFinEquiv.symm i with
      | inl j => simpa [h, ωB] using Nat.succ_le_succ (hωP j)
      | inr j => simp [h, ωB]
    · intro d
      rw [span_reindex_weight]
      cases d with
      | zero => simpa [hzero] using B.span_eq
      | succ d =>
        rw [span_complementBasis_weight_succ, hbP]
        change ((F (d + 1)).comap P.subtype).map P.subtype = F (d + 1)
        rw [Submodule.map_comap_subtype, inf_eq_right]
        exact hmono (Nat.succ_le_succ (Nat.zero_le d))

end EnvelopingIsomorphism.LinearAlgebra
