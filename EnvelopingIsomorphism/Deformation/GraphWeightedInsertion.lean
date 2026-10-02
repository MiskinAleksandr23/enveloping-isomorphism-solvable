import EnvelopingIsomorphism.Deformation.GraphCoefficientProfiles
import EnvelopingIsomorphism.Deformation.UniformBinaryGraphs

/-! Actual finite scalar profiles of weighted graph insertion.
The profile records products of weights and every admissible incoming-arrow
assignment; evaluating it gives the corresponding insertion of actual cochains. -/

noncomputable section
set_option maxSynthPendingDepth 3

namespace EnvelopingIsomorphism.Deformation.GraphWeightedInsertion

open scoped BigOperators Classical
open UniformBinaryGraphs

variable {k : Type*} [CommRing k] {a b d : ℕ}

abbrev Bivector := Multiderivation k (MvPolynomial (Fin d) k) 2

def binaryValue (π : Bivector (k := k) (d := d)) (Γ : BinaryGraph a 2) :
    Binary k (MvPolynomial (Fin d) k) :=
  cochainTwoEquiv k _ (operator Γ (fun _ ↦ π))

def ternaryValue (π : Bivector (k := k) (d := d)) (Γ : BinaryGraph a 3) :
    Ternary k (MvPolynomial (Fin d) k) :=
  cochainThreeEquiv k _ (operator Γ (fun _ ↦ π))

def weightedBinary (w : BinaryGraph a 2 → k) (π : Bivector (k := k) (d := d)) :
    Binary k (MvPolynomial (Fin d) k) := ∑ Γ, w Γ • binaryValue π Γ

/-- Finite data for one genuine target-side boundary insertion. -/
abbrev GraftIndex (a b : ℕ) (r : Fin 2) :=
  (Γ : BinaryGraph a 2) × (_ : BinaryGraph b 2) × GraftChoices (b := b) Γ r

def graftGraph (r : Fin 2) (i : GraftIndex a b r) : BinaryGraph (a + b) 3 :=
  uniformGraft i.1 i.2.1 r i.2.2

/-- A pure scalar sum: only graph targets, actual weights and finite assignments occur. -/
def graftProfile (r : Fin 2) (w : BinaryGraph a 2 → k) (v : BinaryGraph b 2 → k) :
    BinaryGraph (a + b) 3 → k :=
  GraphCoefficientProfiles.pushforward (graftGraph r) (fun i ↦ w i.1 * v i.2.1)

theorem graftProfile_apply (r : Fin 2) (w : BinaryGraph a 2 → k) (v : BinaryGraph b 2 → k)
    (H : BinaryGraph (a + b) 3) :
    graftProfile r w v H =
      ∑ Γ : BinaryGraph a 2, ∑ Δ : BinaryGraph b 2, ∑ χ : GraftChoices (b := b) Γ r,
        if uniformGraft Γ Δ r χ = H then w Γ * v Δ else 0 := by
  unfold graftProfile GraphCoefficientProfiles.pushforward
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  rw [Fintype.sum_sigma]
  rfl

theorem constant_addCases (π : Bivector (k := k) (d := d)) :
    Fin.addCases (fun _ : Fin a ↦ π) (fun _ : Fin b ↦ π) = fun _ ↦ π := by
  funext i
  refine Fin.addCases (fun _ ↦ ?_) (fun _ ↦ ?_) i <;> simp

theorem evaluation_graftProfile (r : Fin 2) (w : BinaryGraph a 2 → k) (v : BinaryGraph b 2 → k)
    (π : Bivector (k := k) (d := d)) :
    GraphCoefficientProfiles.evaluation (ternaryValue π) (graftProfile r w v) =
      ∑ Γ : BinaryGraph a 2, ∑ Δ : BinaryGraph b 2,
        (w Γ * v Δ) • cochainThreeEquiv k _
          (graftOperatorSum Γ Δ r (fun _ ↦ π) (fun _ ↦ π)) := by
  rw [graftProfile, GraphCoefficientProfiles.evaluation_pushforward, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro Δ hΔ
  rw [graftOperatorSum, constant_addCases, map_sum, Finset.smul_sum]
  rfl

theorem insertLeft_weightedBinary (w : BinaryGraph a 2 → k) (v : BinaryGraph b 2 → k)
    (π : Bivector (k := k) (d := d)) :
    insertLeft (weightedBinary w π) (weightedBinary v π) =
      ∑ Γ : BinaryGraph a 2, ∑ Δ : BinaryGraph b 2,
        (w Γ * v Δ) • insertLeft (binaryValue π Γ) (binaryValue π Δ) := by
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro g
  apply LinearMap.ext
  intro h
  simp [insertLeft_apply, weightedBinary, map_sum, map_smul]
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp [mul_comm]

theorem insertRight_weightedBinary (w : BinaryGraph a 2 → k) (v : BinaryGraph b 2 → k)
    (π : Bivector (k := k) (d := d)) :
    insertRight (weightedBinary w π) (weightedBinary v π) =
      ∑ Γ : BinaryGraph a 2, ∑ Δ : BinaryGraph b 2,
        (w Γ * v Δ) • insertRight (binaryValue π Γ) (binaryValue π Δ) := by
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro g
  apply LinearMap.ext
  intro h
  simp [insertRight_apply, weightedBinary, map_sum, map_smul]
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp [mul_comm]

/-- Pure scalar graft coefficients evaluate to the actual left composition. -/
theorem evaluation_graftProfile_left (w : BinaryGraph a 2 → k) (v : BinaryGraph b 2 → k)
    (π : Bivector (k := k) (d := d)) :
    GraphCoefficientProfiles.evaluation (ternaryValue π) (graftProfile 0 w v) =
      insertLeft (weightedBinary w π) (weightedBinary v π) := by
  rw [evaluation_graftProfile, insertLeft_weightedBinary]
  simp only [graftOperatorSum_left]
  rfl

/-- Pure scalar graft coefficients evaluate to the actual right composition. -/
theorem evaluation_graftProfile_right (w : BinaryGraph a 2 → k) (v : BinaryGraph b 2 → k)
    (π : Bivector (k := k) (d := d)) :
    GraphCoefficientProfiles.evaluation (ternaryValue π) (graftProfile 1 w v) =
      insertRight (weightedBinary w π) (weightedBinary v π) := by
  rw [evaluation_graftProfile, insertRight_weightedBinary]
  simp only [graftOperatorSum_right]
  rfl

end EnvelopingIsomorphism.Deformation.GraphWeightedInsertion
