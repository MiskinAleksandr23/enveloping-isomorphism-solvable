import EnvelopingIsomorphism.Deformation.Kontsevich.GeometricOneVertex
import EnvelopingIsomorphism.Deformation.GeneralGraphUnit
import EnvelopingIsomorphism.Deformation.GraphLieGenerators

/-! The actual effective graph weights for binary products, with genuine
one-vertex normalization and unit laws derived from vanishing densities. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.GeometricWeights

open scoped BigOperators

theorem binaryEdgeCount (n : ℕ) :
    ∑ _ : Fin (n + 1), 2 = GraphForms.dimension n 2 := by
  simp [GraphForms.dimension, Nat.add_mul]

/-- The effective coefficient for a graph with n+1 internal bivector vertices.
The weight is the genuine normalized integral divided by (n+1)!. -/
def binaryWeight (n : ℕ) (Γ : KontsevichGraph (n + 1)) : ℝ :=
  canonicalEffectiveWeight (KontsevichGraph.General.ofBinary Γ) (binaryEdgeCount n)

theorem ofBinary_oneVertex (Γ : KontsevichGraph 1) :
    KontsevichGraph.General.ofBinary Γ = oneVertexGraph 2 (oneVertexGraphPermutation Γ) := by
  apply KontsevichGraph.General.Graph.ext
  funext e
  exact oneVertexGraphPermutation_target Γ e.1 e.2

/-- The previously computed +1/4 and -1/4 are exactly the general integral weights. -/
theorem binaryWeight_oneVertex (Γ : KontsevichGraph 1) :
    binaryWeight 0 Γ = geometricOneVertexGraphWeight Γ := by
  rw [binaryWeight, ofBinary_oneVertex]
  exact canonicalEffectiveWeight_oneVertex ⟨2, by decide⟩ (oneVertexGraphPermutation Γ)

theorem binaryWeight_eq_zero_of_untargeted (n : ℕ) (Γ : KontsevichGraph (n + 1))
    (j : Fin 2) (hj : ∀ e, Γ.target e ≠ Sum.inr j) : binaryWeight n Γ = 0 := by
  apply canonicalEffectiveWeight_eq_zero_of_untargeted _ _ j
  intro e
  exact hj (e.1, e.2)

theorem binaryWeight_eq_zero_of_incoming_empty (n : ℕ) (Γ : KontsevichGraph (n + 1))
    (j : Fin 2) (hj : Γ.incoming (Sum.inr j) = ∅) : binaryWeight n Γ = 0 := by
  apply binaryWeight_eq_zero_of_untargeted n Γ j
  intro e he
  have hm : e ∈ Γ.incoming (Sum.inr j) := by simp [KontsevichGraph.incoming, he]
  rw [hj] at hm
  exact Finset.notMem_empty _ hm

variable (R : Type*) [CommRing R] [Algebra ℝ R]

/-- The same universal real weights in the actual coefficient algebra. -/
def binaryWeightOver (n : ℕ) (Γ : KontsevichGraph (n + 1)) : R :=
  algebraMap ℝ R (binaryWeight n Γ)

@[simp] theorem binaryWeightOver_oneVertex (Γ : KontsevichGraph 1) :
    binaryWeightOver R 0 Γ = algebraMap ℝ R (geometricOneVertexGraphWeight Γ) := by
  rw [binaryWeightOver, binaryWeight_oneVertex]

theorem binaryWeightOver_eq_zero_of_incoming_empty (n : ℕ) (Γ : KontsevichGraph (n + 1))
    (j : Fin 2) (hj : Γ.incoming (Sum.inr j) = ∅) : binaryWeightOver R n Γ = 0 := by
  rw [binaryWeightOver, binaryWeight_eq_zero_of_incoming_empty n Γ j hj, map_zero]

/-- These are exactly the effective weights in the existing actual F10/F11 construction. -/
theorem geometricFirstWeights_eq_binaryWeightOver :
    KontsevichGraph.geometricFirstWeights (fun n Γ ↦ binaryWeightOver R (n + 1) Γ) =
      binaryWeightOver R := by
  funext n
  cases n with
  | zero => funext Γ; exact (binaryWeightOver_oneVertex R Γ).symm
  | succ n => rfl

variable [Nontrivial R] {d : ℕ}

/-- Left unity follows from actual vanishing weights for graphs missing the first input. -/
theorem polynomialProduct_one_left (c : Fin d → Fin d → Fin d → R)
    (f : KontsevichGraph.Polynomial d R) :
    KontsevichGraph.polynomialProduct (fun _ ↦ Finset.univ) (binaryWeightOver R) c 1 f = f := by
  rw [KontsevichGraph.polynomialProduct_eq_finiteStarOperator _ _ _ 1 f
    (f.totalDegree + 1) (by simp)]
  apply KontsevichGraph.General.finiteStarOperator_one_left
  intro n hn Γ hΓ hmissing
  exact binaryWeightOver_eq_zero_of_incoming_empty R n Γ 0 hmissing

/-- The corresponding right unit law uses the same actual integral definition. -/
theorem polynomialProduct_one_right (c : Fin d → Fin d → Fin d → R)
    (f : KontsevichGraph.Polynomial d R) :
    KontsevichGraph.polynomialProduct (fun _ ↦ Finset.univ) (binaryWeightOver R) c f 1 = f := by
  rw [KontsevichGraph.polynomialProduct_eq_finiteStarOperator _ _ _ f 1
    (f.totalDegree + 1) (by simp)]
  apply KontsevichGraph.General.finiteStarOperator_one_right
  intro n hn Γ hΓ hmissing
  exact binaryWeightOver_eq_zero_of_incoming_empty R n Γ 1 hmissing

/-- For these genuine weights, only associativity remains to construct the
product-law bundle; both unit equations have already been proved. -/
theorem productLaws_of_associative (c : Fin d → Fin d → Fin d → R)
    (h : ∀ f g p,
      KontsevichGraph.polynomialProduct (fun _ ↦ Finset.univ) (binaryWeightOver R) c
        (KontsevichGraph.polynomialProduct (fun _ ↦ Finset.univ) (binaryWeightOver R) c f g) p =
      KontsevichGraph.polynomialProduct (fun _ ↦ Finset.univ) (binaryWeightOver R) c f
        (KontsevichGraph.polynomialProduct (fun _ ↦ Finset.univ) (binaryWeightOver R) c g p)) :
    KontsevichGraph.ProductLaws (fun _ ↦ Finset.univ) (binaryWeightOver R) c where
  associative := h
  one_mul := polynomialProduct_one_left R c
  mul_one := polynomialProduct_one_right R c

end EnvelopingIsomorphism.Deformation.Kontsevich.GeometricWeights
