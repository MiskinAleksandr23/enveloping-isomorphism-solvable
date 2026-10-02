import EnvelopingIsomorphism.Deformation.GeneralGraphMixedProfiles
import EnvelopingIsomorphism.Deformation.GraphCoefficientProfiles
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp

/-! Literal signed outgoing averaging for arbitrary dependent source arities,
including the exact stabilizer multiplicity of any binary outgoing row. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.GeneralGraphOutgoingAverage
open KontsevichGraph.General
open scoped Classical BigOperators
variable {n m : ℕ} {q : Fin n → ℕ}

abbrev Group (q : Fin n → ℕ) := (v : Fin n) → Equiv.Perm (Fin (q v))

def sign (τ : Group q) : ℝ := ∏ v, permutationSign (R := ℝ) (τ v)

def average (c : Graph q m → ℝ) (H : Graph q m) : ℝ :=
  (Fintype.card (Group q) : ℝ)⁻¹ * ∑ τ : Group q, sign τ * c (H.permuteOutgoing (fun v ↦ (τ v).symm))

theorem sign_sq (τ : Group q) : sign τ * sign τ = 1 := by
  rw [sign,← Finset.prod_mul_distrib]
  have hs (v : Fin n) : permutationSign (R := ℝ) (τ v) * permutationSign (τ v) = 1 := by
    simp [permutationSign,← Int.cast_mul,← Units.val_mul]
  simp only [hs,Finset.prod_const_one]

theorem sign_mul (σ τ : Group q) : sign (σ * τ) = sign σ * sign τ := by
  simp [sign,permutationSign,Equiv.Perm.sign_mul,Finset.prod_mul_distrib]

theorem sign_symm (τ : Group q) : sign (fun v ↦ (τ v).symm) = sign τ := by
  simp [sign,permutationSign]

theorem permute_cancel_right (H : Graph q m) (σ τ : Group q) :
    (H.permuteOutgoing σ).permuteOutgoing (fun v ↦ ((τ * σ) v).symm) =
      H.permuteOutgoing (fun v ↦ (τ v).symm) := by
  apply Graph.ext
  funext e
  rcases e with ⟨v,j⟩
  change H.target ⟨v,σ v (((τ v) * (σ v)).symm j)⟩ = H.target ⟨v,(τ v).symm j⟩
  congr 2
  apply (τ v).injective
  change ((τ v) * (σ v)) (((τ v) * (σ v)).symm j) = (τ v) ((τ v).symm j)
  simp

theorem average_permuteOutgoing (c : Graph q m → ℝ) (H : Graph q m) (σ : Group q) :
    average c (H.permuteOutgoing σ) = sign σ * average c H := by
  unfold average
  rw [← Equiv.sum_comp (Equiv.mulRight σ)]
  change (Fintype.card (Group q) : ℝ)⁻¹ * (∑ τ : Group q, sign (τ * σ) *
    c ((H.permuteOutgoing σ).permuteOutgoing (fun v ↦ ((τ * σ) v).symm))) = _
  simp only [permute_cancel_right,sign_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  ring

/-- Fixing one outgoing row leaves precisely the independent rows elsewhere. -/
def stabilizerEquiv (v : Fin n) : {τ : Group q // τ v = Equiv.refl _} ≃
    ((w : {w : Fin n // w ≠ v}) → Equiv.Perm (Fin (q w))) where
  toFun τ w := τ.val w.val
  invFun f := ⟨(Equiv.piSplitAt v (fun w ↦ Equiv.Perm (Fin (q w)))).symm (Equiv.refl _,f), by simp⟩
  left_inv τ := by
    apply Subtype.ext
    apply (Equiv.piSplitAt v (fun w ↦ Equiv.Perm (Fin (q w)))).injective
    rw [Equiv.apply_symm_apply]
    apply Prod.ext
    · exact τ.property.symm
    · rfl
  right_inv f := by
    funext w
    simp [Equiv.piSplitAt,w.property]

/-- At a binary row exactly half of all dependent outgoing families fix it. -/
theorem card_group_binary (v : Fin n) (hv : q v = 2) :
    Fintype.card (Group q) = 2 * Fintype.card {τ : Group q // τ v = Equiv.refl _} := by
  rw [Fintype.card_congr (Equiv.piSplitAt v (fun w ↦ Equiv.Perm (Fin (q w))))]
  rw [Fintype.card_prod,Fintype.card_congr (stabilizerEquiv (q := q) v),Fintype.card_perm,hv]
  rfl

theorem stabilizer_ratio_binary (v : Fin n) (hv : q v = 2) :
    (Fintype.card (Group q) : ℝ)⁻¹ * Fintype.card {τ : Group q // τ v = Equiv.refl _} = 1 / 2 := by
  have : Nonempty {τ : Group q // τ v = Equiv.refl _} := ⟨⟨fun _ ↦ Equiv.refl _,rfl⟩⟩
  have hc : (Fintype.card {τ : Group q // τ v = Equiv.refl _} : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [card_group_binary v hv,Nat.cast_mul,Nat.cast_ofNat]
  field_simp

end EnvelopingIsomorphism.Deformation.GeneralGraphOutgoingAverage
