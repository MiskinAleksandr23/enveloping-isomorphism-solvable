import EnvelopingIsomorphism.Deformation.Gauge.PlacedMixedGraphTaylorCoefficients
import EnvelopingIsomorphism.Deformation.GeneralGraphMixedProfiles
import EnvelopingIsomorphism.Deformation.GraphCoefficientProfiles

/-! The actual one-vector graph carrier used by mixed scalar boundary profiles.
The external arity is independent of the distinguished vertex arity. -/

noncomputable section
set_option maxSynthPendingDepth 3
namespace EnvelopingIsomorphism.Deformation.MixedGraphProfileCarrier
open scoped BigOperators Classical
open KontsevichGraph.General

abbrev VectorGraph (n m : ℕ) :=
  (i : Fin (n + 1)) × Graph (Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 i) m

abbrev VectorGraph.vertex {n m : ℕ} (Γ : VectorGraph n m) : Fin (n + 1) := Γ.1
abbrev VectorGraph.graph {n m : ℕ} (Γ : VectorGraph n m) := Γ.2

variable {k : Type*} [CommRing k] {n m d : ℕ}

abbrev Bivector := Multiderivation k (MvPolynomial (Fin d) k) 2
abbrev Vector := Multiderivation k (MvPolynomial (Fin d) k) 1

def pairGraphCoefficient (Γ : VectorGraph n m) :
    MultilinearMap k (fun _ : Fin (n + 1) ↦ Gauge.PlacedMixedGraphTaylorCoefficients.PairInput k d 1)
      (Cochain k (MvPolynomial (Fin d) k) m) :=
  Γ.graph.cochainOperator.compLinearMap (Gauge.PlacedMixedGraphTaylorCoefficients.vertexTensor 1 Γ.vertex)

def distinguish :
    MultilinearMap k (fun _ : Fin 1 ↦ Gauge.PlacedMixedGraphTaylorCoefficients.PairInput k d 1)
      (Cochain k (MvPolynomial (Fin d) k) m) →ₗ[k]
      (Vector (k := k) (d := d) →ₗ[k] Cochain k (MvPolynomial (Fin d) k) m) :=
  (MultilinearMap.ofSubsingletonₗ k k _ _ (0 : Fin 1)).symm.toLinearMap.comp
    (MultilinearMap.compLinearMapₗ (fun _ : Fin 1 ↦ LinearMap.inl k _ _))

/-- The genuine graph operation keeps the vector argument linear and the n
independent bivectors in the increasing order of its actual complement. -/
def operator (Γ : VectorGraph n m) :
    MultilinearMap k (fun _ : Fin n ↦ Bivector (k := k) (d := d))
      (Vector (k := k) (d := d) →ₗ[k] Cochain k (MvPolynomial (Fin d) k) m) :=
  distinguish.compMultilinearMap
    (((MultilinearMap.curryFinFinset k _ _
      (Gauge.PlacedMixedGraphTaylorCoefficients.card_bivectorSlots Γ.vertex)
      (Gauge.PlacedMixedGraphTaylorCoefficients.card_bivectorSlots_compl Γ.vertex))
      (pairGraphCoefficient Γ)).compLinearMap (fun _ ↦ LinearMap.inr k _ _))

@[simp] theorem operator_apply (Γ : VectorGraph n m)
    (R : Fin n → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    operator Γ R X = Γ.graph.cochainOperator (fun v ↦
      Gauge.PlacedMixedGraphTaylorCoefficients.vertexTensor 1 Γ.vertex v
        (Gauge.PlacedMixedGraphTaylorCoefficients.orderedInput Γ.vertex R X v)) := rfl

/-- Unary graph values are exactly the existing all-position velocity coefficients. -/
theorem operator_unary_eq_placed (i : Fin (n + 1))
    (Γ : Gauge.PlacedMixedGraphTaylorCoefficients.Graph 1 i) :
    operator (k := k) (d := d) (⟨i, Γ⟩ : VectorGraph n 1) =
      Gauge.PlacedMixedGraphTaylorCoefficients.graphCoefficient i Γ := rfl

def binaryValue (Γ : VectorGraph n 2) :
    MultilinearMap k (fun _ : Fin n ↦ Bivector (k := k) (d := d))
      (Vector (k := k) (d := d) →ₗ[k] Binary k (MvPolynomial (Fin d) k)) :=
  (LinearMap.llcomp k _ _ _ (cochainTwoEquiv k (MvPolynomial (Fin d) k)).toLinearMap).compMultilinearMap
    (operator Γ)

def unaryValue (Γ : VectorGraph n 1) :
    MultilinearMap k (fun _ : Fin n ↦ Bivector (k := k) (d := d))
      (Vector (k := k) (d := d) →ₗ[k] Unary k (MvPolynomial (Fin d) k)) :=
  (LinearMap.llcomp k _ _ _ (cochainOneEquiv k (MvPolynomial (Fin d) k)).toLinearMap).compMultilinearMap
    (operator Γ)

/-- Equal arity profiles embed a genuine graph in the labelled one-vector carrier. -/
def ofProfile {q : Fin (n + 1) → ℕ} (i : Fin (n + 1))
    (h : q = Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 i) (Γ : Graph q m) : VectorGraph n m :=
  ⟨i, h ▸ Γ⟩

/-- Transport only the proved total vertex count, leaving actual labels intact. -/
def castVertices {N : ℕ} (h : n = N) (Γ : VectorGraph n m) : VectorGraph N m := h ▸ Γ

abbrev placementEquiv (i : Fin (n + 1)) : Fin n ⊕ Fin 1 ≃ Fin (n + 1) :=
  finSumEquivOfFinset (Gauge.PlacedMixedGraphTaylorCoefficients.card_bivectorSlots i)
    (Gauge.PlacedMixedGraphTaylorCoefficients.card_bivectorSlots_compl i)

theorem placementEquiv_inl_ne (i : Fin (n + 1)) (j : Fin n) :
    placementEquiv i (Sum.inl j) ≠ i := by
  have h := Finset.orderEmbOfFin_mem
    (Gauge.PlacedMixedGraphTaylorCoefficients.bivectorSlots i)
    (Gauge.PlacedMixedGraphTaylorCoefficients.card_bivectorSlots i) j
  simp only [Gauge.PlacedMixedGraphTaylorCoefficients.bivectorSlots,
    Finset.mem_compl, Finset.mem_singleton] at h
  exact h

theorem placementEquiv_inr (i : Fin (n + 1)) (j : Fin 1) :
    placementEquiv i (Sum.inr j) = i := by
  simp [placementEquiv, Gauge.PlacedMixedGraphTaylorCoefficients.bivectorSlots]

/-- Arbitrary background bivectors indexed by all vertices; the value at the
distinguished vector vertex is ignored. This API is convenient for graph splits. -/
def rawTensors (i : Fin (n + 1)) (B : Fin (n + 1) → Bivector (k := k) (d := d))
    (X : Vector (k := k) (d := d)) (v : Fin (n + 1)) :
    Tensor (Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 i v) d k :=
  Gauge.PlacedMixedGraphTaylorCoefficients.vertexTensor 1 i v
    (if v = i then (X, 0) else (0, B v))

def rawValue (Γ : VectorGraph n m) (B : Fin (n + 1) → Bivector (k := k) (d := d))
    (X : Vector (k := k) (d := d)) : Cochain k (MvPolynomial (Fin d) k) m :=
  Γ.graph.cochainOperator (rawTensors Γ.vertex B X)

theorem operator_eq_rawValue (Γ : VectorGraph n m)
    (B : Fin (n + 1) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    operator Γ (fun j ↦ B (placementEquiv Γ.vertex (Sum.inl j))) X = rawValue Γ B X := by
  rw [operator_apply]
  apply congrArg Γ.graph.cochainOperator
  funext v
  apply congrArg (Gauge.PlacedMixedGraphTaylorCoefficients.vertexTensor 1 Γ.vertex v)
  obtain ⟨s, rfl⟩ := (placementEquiv Γ.vertex).surjective v
  change Sum.elim (fun j ↦ (0, B (placementEquiv Γ.vertex (Sum.inl j))))
    (fun _ : Fin 1 ↦ (X, 0)) ((placementEquiv Γ.vertex).symm (placementEquiv Γ.vertex s)) = _
  rw [Equiv.symm_apply_apply]
  cases s with
  | inl j => rw [if_neg (placementEquiv_inl_ne Γ.vertex j)]; rfl
  | inr j => rw [if_pos (placementEquiv_inr Γ.vertex j)]; rfl

def weightedVelocity (w : VectorGraph n 1 → k) :=
  GraphCoefficientProfiles.evaluation (unaryValue (k := k) (d := d)) w

/-- The weighted carrier is exactly the current placed velocity Taylor family,
with every distinguished position and its original scalar coefficient. -/
theorem weightedVelocity_eq_placed
    (w : (j : ℕ) → (i : Fin (j + 1)) → Gauge.PlacedMixedGraphTaylorCoefficients.Graph 1 i → k) :
    weightedVelocity (k := k) (d := d) (fun Γ : VectorGraph n 1 ↦ w n Γ.vertex Γ.graph) =
      Gauge.PlacedMixedGraphTaylorCoefficients.velocityFamily (fun _ _ ↦ Finset.univ) w n := by
  apply MultilinearMap.ext
  intro R
  apply LinearMap.ext
  intro X
  simp only [weightedVelocity, GraphCoefficientProfiles.evaluation_apply,
    sum_apply, smul_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    unaryValue, LinearMap.compMultilinearMap_apply, LinearMap.llcomp_apply]
  rw [Fintype.sum_sigma]
  simp [Gauge.PlacedMixedGraphTaylorCoefficients.velocityFamily,
    Gauge.PlacedMixedGraphTaylorCoefficients.mapOutput,
    Gauge.PlacedMixedGraphTaylorCoefficients.effectiveFamily_apply,
    operator_unary_eq_placed, map_sum, map_smul]

end EnvelopingIsomorphism.Deformation.MixedGraphProfileCarrier
