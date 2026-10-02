import EnvelopingIsomorphism.Deformation.GraphCoefficientProfiles
import EnvelopingIsomorphism.Deformation.GeneralGraphInsertionLow

/-! Scalar graft profiles for arbitrary actual arity profiles, including the
unary/binary graph compositions in the mixed gauge boundary identity. -/

noncomputable section
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.GraphGeneralWeightedGraft
open scoped BigOperators Classical
open KontsevichGraph.General GraphCoefficientProfiles

variable {k : Type*} [CommRing k] {a b m l d : ℕ}
  {q : Fin a → ℕ} {p : Fin b → ℕ}

abbrev GraftIndex (q : Fin a → ℕ) (p : Fin b → ℕ) (r : Fin (m + 1)) :=
  (Γ : Graph q (m + 1)) × (_ : Graph p (l + 1)) × Γ.GraftChoices (b := b) (l := l) r

def graftProfile (r : Fin (m + 1))
    (w : Graph q (m + 1) → k) (v : Graph p (l + 1) → k) :
    Graph (graftArity q p) (m + l + 1) → k :=
  pushforward (fun i : GraftIndex (l := l) q p r ↦ i.1.graft i.2.1 r i.2.2)
    (fun i ↦ w i.1 * v i.2.1)

theorem graftProfile_apply (r : Fin (m + 1))
    (w : Graph q (m + 1) → k) (v : Graph p (l + 1) → k)
    (H : Graph (graftArity q p) (m + l + 1)) :
    graftProfile r w v H = ∑ Γ : Graph q (m + 1), ∑ Δ : Graph p (l + 1),
      ∑ χ : Γ.GraftChoices (b := b) (l := l) r,
        if Γ.graft Δ r χ = H then w Γ * v Δ else 0 := by
  rw [graftProfile, pushforward, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  rw [Fintype.sum_sigma]

def cochainValue (T : (v : Fin a) → Tensor (q v) d k) (Γ : Graph q m) :
    Cochain k (MvPolynomial (Fin d) k) m := Γ.cochainOperator T

def weightedCochain (w : Graph q m → k) (T : (v : Fin a) → Tensor (q v) d k) :
    Cochain k (MvPolynomial (Fin d) k) m := ∑ Γ, w Γ • cochainValue T Γ

/-- Every graft assignment, arbitrary input tensor and original scalar weight
is retained before any relabelling or antisymmetrization. -/
theorem evaluation_graftProfile (r : Fin (m + 1))
    (w : Graph q (m + 1) → k) (v : Graph p (l + 1) → k)
    (T : (v : Fin a) → Tensor (q v) d k) (U : (v : Fin b) → Tensor (p v) d k) :
    evaluation (cochainValue (graftTensors q p T U)) (graftProfile r w v) =
      ∑ Γ : Graph q (m + 1), ∑ Δ : Graph p (l + 1),
        (w Γ * v Δ) • Graph.graftCochainSum Γ Δ r T U := by
  rw [graftProfile, evaluation_pushforward, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro Δ hΔ
  rw [Graph.graftCochainSum, Finset.smul_sum]
  rfl

def weightedUnary (w : Graph q 1 → k) (T : (v : Fin a) → Tensor (q v) d k) :
    Unary k (MvPolynomial (Fin d) k) := cochainOneEquiv k _ (weightedCochain w T)

def weightedBinary (w : Graph q 2 → k) (T : (v : Fin a) → Tensor (q v) d k) :
    Binary k (MvPolynomial (Fin d) k) := cochainTwoEquiv k _ (weightedCochain w T)

/-- Actual scalar output-graft coefficients evaluate to postcomposition by
the weighted unary operator. -/
theorem evaluation_unary_output (w : Graph q 1 → k) (v : Graph p 2 → k)
    (T : (v : Fin a) → Tensor (q v) d k) (U : (v : Fin b) → Tensor (p v) d k) :
    cochainTwoEquiv k _
      (evaluation (cochainValue (graftTensors q p T U)) (graftProfile 0 w v)) =
      (weightedBinary v U).compr₂ (weightedUnary w T) := by
  rw [evaluation_graftProfile (m := 0) (l := 1) 0 w v T U, map_sum]
  simp only [map_sum, map_smul, Graph.graft_unary_output]
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro g
  simp [weightedUnary, weightedBinary, weightedCochain, cochainValue,
    map_sum, map_smul, LinearMap.compr₂_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp [mul_comm]

theorem evaluation_unary_left (w : Graph q 2 → k) (v : Graph p 1 → k)
    (T : (v : Fin a) → Tensor (q v) d k) (U : (v : Fin b) → Tensor (p v) d k) :
    cochainTwoEquiv k _
      (evaluation (cochainValue (graftTensors q p T U)) (graftProfile 0 w v)) =
      (weightedBinary w T).comp (weightedUnary v U) := by
  rw [evaluation_graftProfile (m := 1) (l := 0) 0 w v T U, map_sum]
  simp only [map_sum, map_smul, Graph.graft_unary_left]
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro g
  simp [weightedUnary, weightedBinary, weightedCochain, cochainValue,
    map_sum, map_smul, LinearMap.comp_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp [mul_comm]

theorem evaluation_unary_right (w : Graph q 2 → k) (v : Graph p 1 → k)
    (T : (v : Fin a) → Tensor (q v) d k) (U : (v : Fin b) → Tensor (p v) d k) :
    cochainTwoEquiv k _
      (evaluation (cochainValue (graftTensors q p T U)) (graftProfile 1 w v)) =
      (weightedBinary w T).compl₂ (weightedUnary v U) := by
  rw [evaluation_graftProfile (m := 1) (l := 0) 1 w v T U, map_sum]
  simp only [map_sum, map_smul, Graph.graft_unary_right]
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro g
  simp [weightedUnary, weightedBinary, weightedCochain, cochainValue,
    map_sum, map_smul, LinearMap.compl₂_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp [mul_comm]

end EnvelopingIsomorphism.Deformation.GraphGeneralWeightedGraft
