import EnvelopingIsomorphism.Deformation.GeneralGraphInsertion
import EnvelopingIsomorphism.Deformation.LowArity

/-! The actual graft sums are the existing binary and unary Hochschild
insertions used by associativity and infinitesimal gauge transport. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.KontsevichGraph.General.Graph

open scoped BigOperators

variable {R : Type*} [CommRing R] {a b m l d : ℕ}
variable {qΓ : Fin a → ℕ} {qΔ : Fin b → ℕ}

def graftCochainSum (Γ : Graph qΓ (m + 1)) (Δ : Graph qΔ (l + 1)) (r : Fin (m + 1))
    (T : (v : Fin a) → Tensor (qΓ v) d R) (U : (v : Fin b) → Tensor (qΔ v) d R) :
    Cochain R (Polynomial d R) (m + l + 1) :=
  ∑ χ : Γ.GraftChoices (b := b) (l := l) r,
    (Γ.graft Δ r χ).cochainOperator (graftTensors qΓ qΔ T U)

theorem graftCochainSum_apply (Γ : Graph qΓ (m + 1)) (Δ : Graph qΔ (l + 1)) (r : Fin (m + 1))
    (T : (v : Fin a) → Tensor (qΓ v) d R) (U : (v : Fin b) → Tensor (qΔ v) d R)
    (f : Fin (m + l + 1) → Polynomial d R) :
    graftCochainSum Γ Δ r T U f = Γ.cochainOperator T
      (Function.update (fun j ↦ f (graftOuterBoundary r j)) r
        (Δ.cochainOperator U (fun j ↦ f (graftInnerBoundary r j)))) := by
  simp only [graftCochainSum, sum_apply]
  exact (Γ.cochainOperator_graft Δ r T U f).symm

private theorem unary_eval (F : Cochain R (Polynomial d R) 1) (x : Polynomial d R) :
    cochainOneEquiv R (Polynomial d R) F x = F ![x] := by
  have h := cochainOneEquiv_symm_apply R (Polynomial d R)
    (cochainOneEquiv R (Polynomial d R) F) ![x]
  rw [LinearEquiv.symm_apply_apply] at h
  exact h.symm

private theorem binary_eval (F : Cochain R (Polynomial d R) 2) (x y : Polynomial d R) :
    cochainTwoEquiv R (Polynomial d R) F x y = F ![x, y] := by
  have h := cochainTwoEquiv_symm_apply R (Polynomial d R)
    (cochainTwoEquiv R (Polynomial d R) F) ![x, y]
  rw [LinearEquiv.symm_apply_apply] at h
  exact h.symm

private theorem ternary_eval (F : Cochain R (Polynomial d R) 3) (x y z : Polynomial d R) :
    cochainThreeEquiv R (Polynomial d R) F x y z = F ![x, y, z] := by
  have h := cochainThreeEquiv_symm_apply R (Polynomial d R)
    (cochainThreeEquiv R (Polynomial d R) F) ![x, y, z]
  rw [LinearEquiv.symm_apply_apply] at h
  exact h.symm

theorem graft_binary_left (Γ : Graph qΓ 2) (Δ : Graph qΔ 2)
    (T : (v : Fin a) → Tensor (qΓ v) d R) (U : (v : Fin b) → Tensor (qΔ v) d R) :
    cochainThreeEquiv R (Polynomial d R) (graftCochainSum Γ Δ 0 T U) =
      insertLeft (cochainTwoEquiv R (Polynomial d R) (Γ.cochainOperator T))
        (cochainTwoEquiv R (Polynomial d R) (Δ.cochainOperator U)) := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  apply LinearMap.ext
  intro z
  rw [ternary_eval, graftCochainSum_apply, insertLeft_apply,
    binary_eval, binary_eval]
  have hi : (fun j : Fin 2 ↦ (![x, y, z] : Fin 3 → Polynomial d R) (graftInnerBoundary (0 : Fin 2) j)) = ![x, y] := by
    funext j
    fin_cases j <;> simp [graftInnerBoundary]
  rw [hi]
  congr 1
  funext j
  fin_cases j <;> simp [graftOuterBoundary]

theorem graft_binary_right (Γ : Graph qΓ 2) (Δ : Graph qΔ 2)
    (T : (v : Fin a) → Tensor (qΓ v) d R) (U : (v : Fin b) → Tensor (qΔ v) d R) :
    cochainThreeEquiv R (Polynomial d R) (graftCochainSum Γ Δ 1 T U) =
      insertRight (cochainTwoEquiv R (Polynomial d R) (Γ.cochainOperator T))
        (cochainTwoEquiv R (Polynomial d R) (Δ.cochainOperator U)) := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  apply LinearMap.ext
  intro z
  rw [ternary_eval, graftCochainSum_apply, insertRight_apply, binary_eval, binary_eval]
  have hi : (fun j : Fin 2 ↦ (![x, y, z] : Fin 3 → Polynomial d R) (graftInnerBoundary (1 : Fin 2) j)) = ![y, z] := by
    funext j
    fin_cases j <;> simp [graftInnerBoundary]
  rw [hi]
  congr 1
  funext j
  fin_cases j <;> simp [graftOuterBoundary]

theorem graft_unary_output (Γ : Graph qΓ 1) (Δ : Graph qΔ 2)
    (T : (v : Fin a) → Tensor (qΓ v) d R) (U : (v : Fin b) → Tensor (qΔ v) d R) :
    cochainTwoEquiv R (Polynomial d R) (graftCochainSum Γ Δ 0 T U) =
      (cochainTwoEquiv R (Polynomial d R) (Δ.cochainOperator U)).compr₂
        (cochainOneEquiv R (Polynomial d R) (Γ.cochainOperator T)) := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rw [binary_eval, graftCochainSum_apply, LinearMap.compr₂_apply, unary_eval, binary_eval]
  have hi : (fun j : Fin 2 ↦ (![x, y] : Fin 2 → Polynomial d R) (graftInnerBoundary (0 : Fin 1) j)) = ![x, y] := by
    funext j
    fin_cases j <;> simp [graftInnerBoundary]
  rw [hi]
  congr 1
  funext j
  fin_cases j
  simp

theorem graft_unary_left (Γ : Graph qΓ 2) (Δ : Graph qΔ 1)
    (T : (v : Fin a) → Tensor (qΓ v) d R) (U : (v : Fin b) → Tensor (qΔ v) d R) :
    cochainTwoEquiv R (Polynomial d R) (graftCochainSum Γ Δ 0 T U) =
      (cochainTwoEquiv R (Polynomial d R) (Γ.cochainOperator T)).comp
        (cochainOneEquiv R (Polynomial d R) (Δ.cochainOperator U)) := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rw [binary_eval, graftCochainSum_apply, LinearMap.comp_apply, binary_eval, unary_eval]
  have hi : (fun j : Fin 1 ↦ (![x, y] : Fin 2 → Polynomial d R) (graftInnerBoundary (0 : Fin 2) j)) = ![x] := by
    funext j
    fin_cases j
    simp [graftInnerBoundary]
  rw [hi]
  congr 1
  funext j
  fin_cases j <;> simp [graftOuterBoundary]

theorem graft_unary_right (Γ : Graph qΓ 2) (Δ : Graph qΔ 1)
    (T : (v : Fin a) → Tensor (qΓ v) d R) (U : (v : Fin b) → Tensor (qΔ v) d R) :
    cochainTwoEquiv R (Polynomial d R) (graftCochainSum Γ Δ 1 T U) =
      (cochainTwoEquiv R (Polynomial d R) (Γ.cochainOperator T)).compl₂
        (cochainOneEquiv R (Polynomial d R) (Δ.cochainOperator U)) := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rw [binary_eval, graftCochainSum_apply, LinearMap.compl₂_apply, binary_eval, unary_eval]
  have hi : (fun j : Fin 1 ↦ (![x, y] : Fin 2 → Polynomial d R) (graftInnerBoundary (1 : Fin 2) j)) = ![y] := by
    funext j
    fin_cases j
    simp [graftInnerBoundary]
  rw [hi]
  congr 1
  funext j
  fin_cases j <;> simp [graftOuterBoundary]

set_option maxSynthPendingDepth 3 in
/-- The two binary grafts have precisely the established Hochschild insertion sign. -/
theorem graft_binary_insertion (Γ : Graph qΓ 2) (Δ : Graph qΔ 2)
    (T : (v : Fin a) → Tensor (qΓ v) d R) (U : (v : Fin b) → Tensor (qΔ v) d R) :
    cochainThreeEquiv R (Polynomial d R)
        (graftCochainSum Γ Δ 0 T U - graftCochainSum Γ Δ 1 T U) =
      insertBinary (cochainTwoEquiv R (Polynomial d R) (Γ.cochainOperator T))
        (cochainTwoEquiv R (Polynomial d R) (Δ.cochainOperator U)) := by
  rw [map_sub, graft_binary_left, graft_binary_right]
  rfl

/-- The three graph grafts give output-minus-inputs, the actual gauge-action sign. -/
theorem graft_unary_action (Γ : Graph qΓ 1) (Δ : Graph qΔ 2)
    (T : (v : Fin a) → Tensor (qΓ v) d R) (U : (v : Fin b) → Tensor (qΔ v) d R) :
    cochainTwoEquiv R (Polynomial d R)
        (graftCochainSum Γ Δ 0 T U - graftCochainSum Δ Γ 0 U T - graftCochainSum Δ Γ 1 U T) =
      unaryAction (cochainOneEquiv R (Polynomial d R) (Γ.cochainOperator T))
        (cochainTwoEquiv R (Polynomial d R) (Δ.cochainOperator U)) := by
  rw [map_sub, map_sub, graft_unary_output, graft_unary_left, graft_unary_right]
  rfl

end EnvelopingIsomorphism.Deformation.KontsevichGraph.General.Graph
