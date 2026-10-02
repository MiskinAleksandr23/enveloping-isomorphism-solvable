import EnvelopingIsomorphism.Deformation.SymmetrizedGraphProfiles
/-! Actual multilinear grouped insertion and its normalized finite graft profiles. -/

noncomputable section
set_option maxSynthPendingDepth 3
namespace EnvelopingIsomorphism.Deformation.SymmetrizedGraphInsertion
open scoped BigOperators Classical
open UniformBinaryGraphs GraphWeightedInsertion GraphCoefficientProfiles SymmetrizedGraphProfiles
variable {k : Type*} [Field k] [CharZero k] {a b d : ℕ}

abbrev BinaryProfileMap (k : Type*) [CommRing k] (d n : ℕ) :=
  MultilinearMap k (fun _ : Fin n ↦ Bivector (k := k) (d := d))
    (Binary k (MvPolynomial (Fin d) k))

/-- Actual weighted binary cochains with independently varying vertex inputs. -/
def binaryMap (w : BinaryGraph a 2 → k) : BinaryProfileMap k d a :=
  ∑ Γ, w Γ • (cochainTwoEquiv k (MvPolynomial (Fin d) k)).toLinearMap.compMultilinearMap (operator Γ)

omit [CharZero k] in
theorem binaryMap_apply (w : BinaryGraph a 2 → k) (R : Fin a → Bivector (k := k) (d := d)) :
    binaryMap w R = ∑ Γ, w Γ • cochainTwoEquiv k _ (operator Γ R) := by
  simp only [binaryMap, sum_apply, smul_apply]
  rfl

/-- Compose two multilinear maps on disjoint groups of inputs through a bilinear insertion. -/
def groupedInsertion
    (B : Binary k (MvPolynomial (Fin d) k) →ₗ[k]
      Binary k (MvPolynomial (Fin d) k) →ₗ[k] Ternary k (MvPolynomial (Fin d) k))
    (F : BinaryProfileMap k d a) (G : BinaryProfileMap k d b) : ProfileMap k d (a + b) :=
  let post : (Binary k (MvPolynomial (Fin d) k) →ₗ[k] Ternary k (MvPolynomial (Fin d) k)) →ₗ[k]
      MultilinearMap k (fun _ : Fin b ↦ Bivector (k := k) (d := d)) (Ternary k (MvPolynomial (Fin d) k)) :=
    { toFun H := H.compMultilinearMap G
      map_add' H K := by apply MultilinearMap.ext; intro R; rfl
      map_smul' r H := by apply MultilinearMap.ext; intro R; rfl }
  (post.compMultilinearMap (B.compMultilinearMap F)).uncurrySum.domDomCongr finSumFinEquiv

omit [CharZero k] in
theorem groupedInsertion_apply
    (B : Binary k (MvPolynomial (Fin d) k) →ₗ[k]
      Binary k (MvPolynomial (Fin d) k) →ₗ[k] Ternary k (MvPolynomial (Fin d) k))
    (F : BinaryProfileMap k d a) (G : BinaryProfileMap k d b)
    (R : Fin (a + b) → Bivector (k := k) (d := d)) :
    groupedInsertion B F G R = B (F (fun i ↦ R (Fin.castAdd b i)))
      (G (fun j ↦ R (Fin.natAdd a j))) := rfl

omit [CharZero k] in
theorem evaluation_symmetrized (c : BinaryGraph a 3 → k) :
    evaluation (symmetrizedValue (k := k) (d := d)) c =
      symmetrize (evaluation (ternaryMap (k := k) (d := d)) c) := by
  simp only [evaluation_apply, map_sum, map_smul, symmetrizedValue]

omit [CharZero k] in
theorem restrict_addCases (R : Fin (a + b) → Bivector (k := k) (d := d)) :
    Fin.addCases (fun i ↦ R (Fin.castAdd b i)) (fun j ↦ R (Fin.natAdd a j)) = R := by
  funext i
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) i <;> simp

omit [CharZero k] in
/-- Every admissible graft assignment is retained before input symmetrization. -/
theorem evaluation_graftProfile_ordered (r : Fin 2)
    (w : BinaryGraph a 2 → k) (v : BinaryGraph b 2 → k)
    (R : Fin (a + b) → Bivector (k := k) (d := d)) :
    evaluation (ternaryMap (k := k) (d := d)) (graftProfile r w v) R =
      ∑ Γ : BinaryGraph a 2, ∑ Δ : BinaryGraph b 2, (w Γ * v Δ) • cochainThreeEquiv k _
        (graftOperatorSum Γ Δ r (fun i ↦ R (Fin.castAdd b i)) (fun j ↦ R (Fin.natAdd a j))) := by
  rw [graftProfile, evaluation_pushforward]
  simp only [sum_apply, smul_apply]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro Δ hΔ
  rw [graftOperatorSum, restrict_addCases, map_sum, Finset.smul_sum]
  rfl


omit [CharZero k] in
theorem groupedInsertion_binaryMap_apply
    (B : Binary k (MvPolynomial (Fin d) k) →ₗ[k]
      Binary k (MvPolynomial (Fin d) k) →ₗ[k] Ternary k (MvPolynomial (Fin d) k))
    (w : BinaryGraph a 2 → k) (v : BinaryGraph b 2 → k)
    (R : Fin (a + b) → Bivector (k := k) (d := d)) :
    groupedInsertion B (binaryMap w) (binaryMap v) R =
      ∑ Γ : BinaryGraph a 2, ∑ Δ : BinaryGraph b 2,
        (w Γ * v Δ) • B (cochainTwoEquiv k _ (operator Γ (fun i ↦ R (Fin.castAdd b i))))
          (cochainTwoEquiv k _ (operator Δ (fun j ↦ R (Fin.natAdd a j)))) := by
  rw [groupedInsertion_apply, binaryMap_apply, binaryMap_apply]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

open EnvelopingIsomorphism.FormalSeries.PowerSeriesModule

omit [CharZero k] in
theorem evaluation_graftProfile_left :
    ∀ (w : BinaryGraph a 2 → k) (v : BinaryGraph b 2 → k),
    evaluation (ternaryMap (k := k) (d := d)) (graftProfile 0 w v) =
      groupedInsertion insertLeftLinear (binaryMap w) (binaryMap v) := by
  intro w v
  apply MultilinearMap.ext
  intro R
  rw [evaluation_graftProfile_ordered, groupedInsertion_binaryMap_apply]
  simp only [graftOperatorSum_left]
  rfl

omit [CharZero k] in
theorem evaluation_graftProfile_right :
    ∀ (w : BinaryGraph a 2 → k) (v : BinaryGraph b 2 → k),
    evaluation (ternaryMap (k := k) (d := d)) (graftProfile 1 w v) =
      groupedInsertion insertRightLinear (binaryMap w) (binaryMap v) := by
  intro w v
  apply MultilinearMap.ext
  intro R
  rw [evaluation_graftProfile_ordered, groupedInsertion_binaryMap_apply]
  simp only [graftOperatorSum_right]
  rfl

omit [CharZero k] in
theorem evaluation_symmetrized_graftProfile_left
    (w : BinaryGraph a 2 → k) (v : BinaryGraph b 2 → k) :
    evaluation (symmetrizedValue (k := k) (d := d)) (graftProfile 0 w v) =
      symmetrize (groupedInsertion insertLeftLinear (binaryMap w) (binaryMap v)) := by
  rw [evaluation_symmetrized, evaluation_graftProfile_left]

omit [CharZero k] in
theorem evaluation_symmetrized_graftProfile_right
    (w : BinaryGraph a 2 → k) (v : BinaryGraph b 2 → k) :
    evaluation (symmetrizedValue (k := k) (d := d)) (graftProfile 1 w v) =
      symmetrize (groupedInsertion insertRightLinear (binaryMap w) (binaryMap v)) := by
  rw [evaluation_symmetrized, evaluation_graftProfile_right]


omit [CharZero k] in
/-- The normalized grouped insertion is the literal sum over all input placements. -/
theorem symmetrize_groupedInsertion_apply
    (B : Binary k (MvPolynomial (Fin d) k) →ₗ[k]
      Binary k (MvPolynomial (Fin d) k) →ₗ[k] Ternary k (MvPolynomial (Fin d) k))
    (F : BinaryProfileMap k d a) (G : BinaryProfileMap k d b)
    (R : Fin (a + b) → Bivector (k := k) (d := d)) :
    symmetrize (groupedInsertion B F G) R = ((a + b).factorial : k)⁻¹ •
      ∑ σ : Equiv.Perm (Fin (a + b)),
        B (F (fun i ↦ R (σ (Fin.castAdd b i))))
          (G (fun j ↦ R (σ (Fin.natAdd a j)))) := by
  simp only [symmetrize_apply, groupedInsertion_apply, Function.comp_apply]

end EnvelopingIsomorphism.Deformation.SymmetrizedGraphInsertion
