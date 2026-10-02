import EnvelopingIsomorphism.Deformation.Gauge.MixedGraphTaylorCoefficients
import EnvelopingIsomorphism.Deformation.Kontsevich.GeometricWeights

/-! Mixed graph coefficients summed over every distinguished internal position.
Each graph retains its own labelled weight and the common total-vertex MC
factorial. No internal-vertex or anchor-change invariance is assumed. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge.PlacedMixedGraphTaylorCoefficients

open MvPolynomial
open FormalSeries
open scoped BigOperators Classical

variable {k : Type*} [CommRing k] {d n r : ℕ}

local instance unaryAddCommGroup : AddCommGroup (Unary k (MvPolynomial (Fin d) k)) :=
  @LinearMap.addCommGroup k k (MvPolynomial (Fin d) k) (MvPolynomial (Fin d) k)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance (RingHom.id k)

local instance binaryAddCommGroup : AddCommGroup (Binary k (MvPolynomial (Fin d) k)) :=
  @LinearMap.addCommGroup k k (MvPolynomial (Fin d) k) (Unary k (MvPolynomial (Fin d) k))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance (RingHom.id k)

local instance ternaryAddCommGroup : AddCommGroup (Ternary k (MvPolynomial (Fin d) k)) :=
  @LinearMap.addCommGroup k k (MvPolynomial (Fin d) k) (Binary k (MvPolynomial (Fin d) k))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance (RingHom.id k)

/-- The distinguished vertex has arity r, and every other vertex has arity two. -/
def arities (r : ℕ) (i : Fin (n + 1)) (v : Fin (n + 1)) : ℕ := if v = i then r else 2

abbrev Graph (r : ℕ) (i : Fin (n + 1)) := KontsevichGraph.General.Graph (arities r i) r

/-- Every distinguished position has the required top-degree number of edges. -/
theorem edgeCount (r : ℕ) (i : Fin (n + 1)) :
    ∑ v, arities r i v = Kontsevich.GraphForms.dimension n r := by
  rw [Fin.sum_univ_succAbove _ i]
  simp [arities, Fin.succAbove_ne, Kontsevich.GraphForms.dimension, Nat.add_comm]

abbrev PairInput (k : Type*) [CommRing k] (d r : ℕ) :=
  Multiderivation k (MvPolynomial (Fin d) k) r × Multiderivation k (MvPolynomial (Fin d) k) 2

/-- A common pair input lets native finite-set currying select the distinguished
and bivector slots while the genuine graph still has heterogeneous arities. -/
def vertexTensor (r : ℕ) (i v : Fin (n + 1)) :
    PairInput k d r →ₗ[k] KontsevichGraph.General.Tensor (arities r i v) d k := by
  by_cases h : v = i
  · have hq : arities r i v = r := if_pos h
    rw [hq]
    exact (MixedGraphTaylorCoefficients.coordinateTensor (k := k) (d := d) r).comp
      (LinearMap.fst k (Multiderivation k (MvPolynomial (Fin d) k) r)
        (Multiderivation k (MvPolynomial (Fin d) k) 2))
  · have hq : arities r i v = 2 := if_neg h
    rw [hq]
    exact (MixedGraphTaylorCoefficients.coordinateTensor (k := k) (d := d) 2).comp
      (LinearMap.snd k (Multiderivation k (MvPolynomial (Fin d) k) r)
        (Multiderivation k (MvPolynomial (Fin d) k) 2))

/-- The selected bivector vertices carry the increasing order inherited from Fin. -/
def bivectorSlots (i : Fin (n + 1)) : Finset (Fin (n + 1)) := {i}ᶜ

@[simp] theorem card_bivectorSlots (i : Fin (n + 1)) : (bivectorSlots i).card = n := by
  simp [bivectorSlots, Finset.card_compl]

@[simp] theorem card_bivectorSlots_compl (i : Fin (n + 1)) : (bivectorSlots i)ᶜ.card = 1 := by
  simp [bivectorSlots]

/-- The actual graph operator, prior to separating its distinguished argument. -/
def pairGraphCoefficient (i : Fin (n + 1)) (Γ : Graph r i) :
    MultilinearMap k (fun _ : Fin (n + 1) ↦ PairInput k d r)
      (Cochain k (MvPolynomial (Fin d) k) r) :=
  Γ.cochainOperator.compLinearMap (vertexTensor r i)

/-- Convert the remaining singleton pair slot into a genuine linear distinguished slot. -/
def distinguish :
    MultilinearMap k (fun _ : Fin 1 ↦ PairInput k d r) (Cochain k (MvPolynomial (Fin d) k) r) →ₗ[k]
      (Multiderivation k (MvPolynomial (Fin d) k) r →ₗ[k] Cochain k (MvPolynomial (Fin d) k) r) :=
  (MultilinearMap.ofSubsingletonₗ k k _ _ (0 : Fin 1)).symm.toLinearMap.comp
    (MultilinearMap.compLinearMapₗ (fun _ : Fin 1 ↦ LinearMap.inl k _ _))

@[simp] theorem distinguish_apply
    (f : MultilinearMap k (fun _ : Fin 1 ↦ PairInput k d r) (Cochain k (MvPolynomial (Fin d) k) r))
    (D : Multiderivation k (MvPolynomial (Fin d) k) r) :
    distinguish f D = f (fun _ ↦ (D, 0)) := rfl

/-- Genuine mixed coefficient at a specified distinguished vertex. The n other
inputs are inserted in increasing order on its complement. -/
def graphCoefficient (i : Fin (n + 1)) (Γ : Graph r i) :
    MultilinearMap k (fun _ : Fin n ↦ Multiderivation k (MvPolynomial (Fin d) k) 2)
      (Multiderivation k (MvPolynomial (Fin d) k) r →ₗ[k] Cochain k (MvPolynomial (Fin d) k) r) :=
  distinguish.compMultilinearMap
    (((MultilinearMap.curryFinFinset k _ _ (card_bivectorSlots i) (card_bivectorSlots_compl i))
      (pairGraphCoefficient i Γ)).compLinearMap (fun _ ↦ LinearMap.inr k _ _))

/-- Explicit ordered insertion of the actual input tensors. -/
def orderedInput (i : Fin (n + 1))
    (F : Fin n → Multiderivation k (MvPolynomial (Fin d) k) 2)
    (D : Multiderivation k (MvPolynomial (Fin d) k) r) (v : Fin (n + 1)) : PairInput k d r :=
  Sum.elim (fun j ↦ (0, F j)) (fun _ : Fin 1 ↦ (D, 0))
    ((finSumEquivOfFinset (card_bivectorSlots i) (card_bivectorSlots_compl i)).symm v)

/-- Equality with the original graph contraction, not an assumed vertex-relabeling law. -/
theorem graphCoefficient_apply (i : Fin (n + 1)) (Γ : Graph r i)
    (F : Fin n → Multiderivation k (MvPolynomial (Fin d) k) 2)
    (D : Multiderivation k (MvPolynomial (Fin d) k) r) :
    graphCoefficient i Γ F D =
      Γ.cochainOperator (fun v ↦ vertexTensor r i v (orderedInput i F D v)) := rfl

/-- On repeated bivectors the finite insertion has the expected actual selected slots. -/
theorem graphCoefficient_diagonal (i : Fin (n + 1)) (Γ : Graph r i)
    (F : Multiderivation k (MvPolynomial (Fin d) k) 2)
    (D : Multiderivation k (MvPolynomial (Fin d) k) r) :
    graphCoefficient i Γ (fun _ ↦ F) D =
      Γ.cochainOperator (fun v ↦ vertexTensor r i v (if v = i then (D, 0) else (0, F))) := by
  change MultilinearMap.curryFinFinset k _ _ (card_bivectorSlots i) (card_bivectorSlots_compl i)
    (pairGraphCoefficient i Γ) (fun _ ↦ (0, F)) (fun _ ↦ (D, 0)) = _
  rw [MultilinearMap.curryFinFinset_apply_const]
  change Γ.cochainOperator (fun v ↦ vertexTensor r i v
    ((bivectorSlots i).piecewise (fun _ ↦ (0, F)) (fun _ ↦ (D, 0)) v)) = _
  congr 1
  funext v
  by_cases h : v = i <;> simp [bivectorSlots, h]

/-- Every labelled distinguished position is retained, each with its own effective weight. -/
def effectiveFamily
    (s : (n : ℕ) → (i : Fin (n + 1)) → Finset (Graph r i))
    (w : (n : ℕ) → (i : Fin (n + 1)) → Graph r i → k) :
    GraphTaylorFamily (k := k) (V := Multiderivation k (MvPolynomial (Fin d) k) 2)
      (W := Multiderivation k (MvPolynomial (Fin d) k) r →ₗ[k] Cochain k (MvPolynomial (Fin d) k) r) :=
  fun n ↦ ∑ i : Fin (n + 1), ∑ Γ ∈ s n i, w n i Γ • graphCoefficient i Γ

@[simp] theorem effectiveFamily_apply
    (s : (n : ℕ) → (i : Fin (n + 1)) → Finset (Graph r i))
    (w : (n : ℕ) → (i : Fin (n + 1)) → Graph r i → k) (n : ℕ)
    (F : Fin n → Multiderivation k (MvPolynomial (Fin d) k) 2)
    (D : Multiderivation k (MvPolynomial (Fin d) k) r) :
    effectiveFamily s w n F D =
      ∑ i : Fin (n + 1), ∑ Γ ∈ s n i, w n i Γ • graphCoefficient i Γ F D := by
  simp only [effectiveFamily, sum_apply, smul_apply, LinearMap.sum_apply, LinearMap.smul_apply]

/-- Genuine linear conversion of external cochains after summing every position. -/
def mapOutput {O : Type*} [AddCommGroup O] [Module k O]
    (e : Cochain k (MvPolynomial (Fin d) k) r →ₗ[k] O)
    (C : GraphTaylorFamily (k := k) (V := Multiderivation k (MvPolynomial (Fin d) k) 2)
      (W := Multiderivation k (MvPolynomial (Fin d) k) r →ₗ[k] Cochain k (MvPolynomial (Fin d) k) r)) :
    GraphTaylorFamily (k := k) (V := Multiderivation k (MvPolynomial (Fin d) k) 2)
      (W := Multiderivation k (MvPolynomial (Fin d) k) r →ₗ[k] O) :=
  fun n ↦ (LinearMap.llcomp k _ _ _ e).compMultilinearMap (C n)

/-- All-position velocity coefficient data. -/
def velocityFamily
    (s : (n : ℕ) → (i : Fin (n + 1)) → Finset (Graph 1 i))
    (w : (n : ℕ) → (i : Fin (n + 1)) → Graph 1 i → k) :=
  mapOutput (O := Unary k (MvPolynomial (Fin d) k))
    (cochainOneEquiv k (MvPolynomial (Fin d) k)).toLinearMap (effectiveFamily s w)

/-- All-position curvature coefficient data. -/
def curvatureFamily
    (s : (n : ℕ) → (i : Fin (n + 1)) → Finset (Graph 3 i))
    (w : (n : ℕ) → (i : Fin (n + 1)) → Graph 3 i → k) :=
  mapOutput (O := Ternary k (MvPolynomial (Fin d) k))
    (cochainThreeEquiv k (MvPolynomial (Fin d) k)).toLinearMap (effectiveFamily s w)

section Normalization

variable [Algebra ℚ k]

/-- Normalize each labelled graph by the total-vertex MC factorial, before
summing over all distinguished positions. No symmetry combines those positions. -/
def geometricFamily
    (s : (n : ℕ) → (i : Fin (n + 1)) → Finset (Graph r i))
    (W : (n : ℕ) → (i : Fin (n + 1)) → Graph r i → k) :=
  effectiveFamily (d := d) s (fun n i Γ ↦ Kontsevich.effectiveMCWeight (n + 1) (W n i Γ))

theorem geometricFamily_apply
    (s : (n : ℕ) → (i : Fin (n + 1)) → Finset (Graph r i))
    (W : (n : ℕ) → (i : Fin (n + 1)) → Graph r i → k) (n : ℕ)
    (F : Fin n → Multiderivation k (MvPolynomial (Fin d) k) 2)
    (D : Multiderivation k (MvPolynomial (Fin d) k) r) :
    geometricFamily s W n F D =
      ∑ i : Fin (n + 1), ∑ Γ ∈ s n i,
        (((n + 1).factorial : ℚ)⁻¹ • W n i Γ) • graphCoefficient i Γ F D :=
  effectiveFamily_apply _ _ n F D

end Normalization

section Laurent

universe u
variable {K : Type u} [Field K]

/-- Actual Laurent velocity tangent data, retaining all distinguished positions. -/
def velocityTangentFamily
    (s : (n : ℕ) → (i : Fin (n + 1)) → Finset (Graph 1 i))
    (w : (n : ℕ) → (i : Fin (n + 1)) → Graph 1 i → K)
    (π₀ : Multiderivation K (MvPolynomial (Fin d) K) 2) :=
  MixedGraphTaylorCoefficients.tangentFamily (K := K)
    (V := Multiderivation K (MvPolynomial (Fin d) K) 2)
    (D := Multiderivation K (MvPolynomial (Fin d) K) 1)
    (O := Unary K (MvPolynomial (Fin d) K)) (velocityFamily s w) π₀

/-- Actual Laurent curvature tangent data, retaining all distinguished positions. -/
def curvatureTangentFamily
    (s : (n : ℕ) → (i : Fin (n + 1)) → Finset (Graph 3 i))
    (w : (n : ℕ) → (i : Fin (n + 1)) → Graph 3 i → K)
    (π₀ : Multiderivation K (MvPolynomial (Fin d) K) 2) :=
  MixedGraphTaylorCoefficients.tangentFamily (K := K)
    (V := Multiderivation K (MvPolynomial (Fin d) K) 2)
    (D := Multiderivation K (MvPolynomial (Fin d) K) 3)
    (O := Ternary K (MvPolynomial (Fin d) K)) (curvatureFamily s w) π₀

variable [Algebra ℝ K]

/-- The actual canonical geometric graph integrals, with their total-vertex
factorial already included individually, summed over every distinguished position. -/
def canonicalFamily
    (s : (n : ℕ) → (i : Fin (n + 1)) → Finset (Graph r i)) :=
  effectiveFamily (k := K) (d := d) s (fun _ i Γ ↦ algebraMap ℝ K
    (Kontsevich.GeometricWeights.canonicalEffectiveWeight Γ (edgeCount r i)))

@[simp] theorem canonicalFamily_apply
    (s : (n : ℕ) → (i : Fin (n + 1)) → Finset (Graph r i)) (n : ℕ)
    (F : Fin n → Multiderivation K (MvPolynomial (Fin d) K) 2)
    (D : Multiderivation K (MvPolynomial (Fin d) K) r) :
    canonicalFamily s n F D = ∑ i : Fin (n + 1), ∑ Γ ∈ s n i,
      algebraMap ℝ K (Kontsevich.GeometricWeights.canonicalEffectiveWeight Γ (edgeCount r i)) •
        graphCoefficient i Γ F D := effectiveFamily_apply _ _ n F D

/-- Concrete all-position velocity data from the actual canonical graph integrals. -/
def canonicalVelocityTangentFamily
    (s : (n : ℕ) → (i : Fin (n + 1)) → Finset (Graph 1 i))
    (π₀ : Multiderivation K (MvPolynomial (Fin d) K) 2) :=
  velocityTangentFamily s (fun _ i Γ ↦ algebraMap ℝ K
    (Kontsevich.GeometricWeights.canonicalEffectiveWeight Γ (edgeCount 1 i))) π₀

/-- Concrete all-position curvature data from the actual canonical graph integrals. -/
def canonicalCurvatureTangentFamily
    (s : (n : ℕ) → (i : Fin (n + 1)) → Finset (Graph 3 i))
    (π₀ : Multiderivation K (MvPolynomial (Fin d) K) 2) :=
  curvatureTangentFamily s (fun _ i Γ ↦ algebraMap ℝ K
    (Kontsevich.GeometricWeights.canonicalEffectiveWeight Γ (edgeCount 3 i))) π₀

variable [CharZero K]

/-- Extending the actual integrals and then dividing by the total-vertex
factorial is exactly the canonical effective-weight construction. -/
theorem canonicalFamily_eq_geometricFamily
    (s : (n : ℕ) → (i : Fin (n + 1)) → Finset (Graph r i)) :
    canonicalFamily (K := K) (d := d) s = geometricFamily s
      (fun _ i Γ ↦ algebraMap ℝ K (Kontsevich.GeometricWeights.canonicalWeight Γ (edgeCount r i))) := by
  apply congrArg (effectiveFamily (k := K) (d := d) s)
  funext n i Γ
  exact Kontsevich.map_effectiveMCWeight (algebraMap ℝ K).toAddMonoidHom (n + 1) _

end Laurent

end EnvelopingIsomorphism.Deformation.Gauge.PlacedMixedGraphTaylorCoefficients
