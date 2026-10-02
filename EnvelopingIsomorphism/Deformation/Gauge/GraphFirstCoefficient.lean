import EnvelopingIsomorphism.Deformation.MultiderivationCoordinateExpansion
import EnvelopingIsomorphism.Deformation.Gauge.MixedGraphTaylorCoefficients
import EnvelopingIsomorphism.Deformation.Kontsevich.GeometricOneVertex

/-! First graph coefficients on arbitrary polynomial multiderivations. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge.GraphFirstCoefficient

open MvPolynomial
open KontsevichGraph.General
open Kontsevich.GeometricWeights
open scoped BigOperators

variable {k : Type*} [CommRing k] {r d : ℕ}

local instance unaryAddCommGroup : AddCommGroup (Unary k (MvPolynomial (Fin d) k)) :=
  @LinearMap.addCommGroup k k (MvPolynomial (Fin d) k) (MvPolynomial (Fin d) k)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance (RingHom.id k)

local instance binaryAddCommGroup : AddCommGroup (Binary k (MvPolynomial (Fin d) k)) :=
  @LinearMap.addCommGroup k k (MvPolynomial (Fin d) k) (Unary k (MvPolynomial (Fin d) k))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance (RingHom.id k)

/-- Coordinate labels for a single vertex are exactly the labels of its outgoing slots. -/
def labelEquiv (r d : ℕ) : (Edge (fun _ : Fin 1 ↦ r) → Fin d) ≃ (Fin r → Fin d) where
  toFun lab a := lab ⟨0, a⟩
  invFun lab e := lab e.2
  left_inv lab := by
    funext e
    rcases e with ⟨v, a⟩
    rw [Fin.eq_zero v]
  right_inv _ := rfl

@[simp] theorem incoming_internal (σ : Equiv.Perm (Fin r)) (v : Fin 1) :
    (oneVertexGraph r σ).incoming (Sum.inl v) = ∅ := by
  classical
  ext e
  simp [Graph.incoming, oneVertexGraph]

@[simp] theorem incoming_external (σ : Equiv.Perm (Fin r)) (j : Fin r) :
    (oneVertexGraph r σ).incoming (Sum.inr j) = {⟨0, σ.symm j⟩} := by
  classical
  ext e
  rcases e with ⟨v, a⟩
  rw [Fin.eq_zero v]
  simp [Graph.incoming, oneVertexGraph, Equiv.apply_eq_iff_eq_symm_apply]

/-- The actual one-vertex contraction, with every finite coordinate labeling retained. -/
theorem oneVertex_cochainOperator_apply (σ : Equiv.Perm (Fin r))
    (T : Tensor r d k) (f : Fin r → MvPolynomial (Fin d) k) :
    (oneVertexGraph r σ).cochainOperator (fun _ ↦ T) f =
      ∑ lab : Fin r → Fin d, T lab * ∏ i, pderiv (lab i) (f (σ i)) := by
  classical
  rw [Graph.cochainOperator_apply]
  simp only [Graph.vertexDerivative, incoming_internal, incoming_external,
    Finset.toList_empty, List.map_nil, iteratedPDeriv, LinearMap.id_apply,
    Fin.prod_univ_one, Finset.toList_singleton, List.map_singleton,
    LinearMap.coe_comp, Function.comp_apply]
  apply Fintype.sum_equiv (labelEquiv r d)
  intro lab
  congr 1
  apply Fintype.prod_equiv σ.symm
  intro i
  simp [labelEquiv]

/-- A one-vertex coordinate graph acts on an arbitrary polynomial multiderivation
by the indicated outgoing permutation, not merely on linear bivectors. -/
theorem oneVertex_raw (σ : Equiv.Perm (Fin r))
    (F : Multiderivation k (MvPolynomial (Fin d) k) r)
    (f : Fin r → MvPolynomial (Fin d) k) :
    (oneVertexGraph r σ).cochainOperator
      (fun _ ↦ MixedGraphTaylorCoefficients.coordinateTensor r F) f = F (fun i ↦ f (σ i)) := by
  rw [oneVertex_cochainOperator_apply]
  exact (Multiderivation.apply_coordinate_expansion r F (fun i ↦ f (σ i))).symm

section Geometric

variable {K : Type*} [Field K] [CharZero K] [Algebra ℝ K]

/-- Actual one-vertex graph contractions with the already evaluated integral weights. -/
def geometricOneVertexCoefficient (m : Fin 4)
    (F : Multiderivation K (MvPolynomial (Fin d) K) m.val) :
    Cochain K (MvPolynomial (Fin d) K) m.val :=
  ∑ σ : Equiv.Perm (Fin m.val),
    algebraMap ℝ K (Kontsevich.labelledOneVertexWeight m σ) •
      (oneVertexGraph m.val σ).cochainOperator
        (fun _ ↦ MixedGraphTaylorCoefficients.coordinateTensor m.val F)

/-- The true geometric one-vertex sum is factorial-normalized raw evaluation
for every polynomial multiderivation, in all verified geometric arities. -/
theorem geometricOneVertexCoefficient_eq_toCochain (m : Fin 4)
    (F : Multiderivation K (MvPolynomial (Fin d) K) m.val) :
    geometricOneVertexCoefficient m F = Multiderivation.toCochain F := by
  classical
  apply MultilinearMap.ext
  intro f
  simp only [geometricOneVertexCoefficient, sum_apply, smul_apply, oneVertex_raw,
    Multiderivation.toCochain_apply]
  have hterm (σ : Equiv.Perm (Fin m.val)) :
      algebraMap ℝ K (Kontsevich.labelledOneVertexWeight m σ) • F (fun i ↦ f (σ i)) =
        ((m.val.factorial : K)⁻¹ ^ 2) • F f := by
    have hp := F.val.map_perm f σ
    change F (fun i ↦ f (σ i)) = Equiv.Perm.sign σ • F f at hp
    rw [hp, Kontsevich.labelledOneVertexWeight_eq, Kontsevich.canonicalOneVertexWeight_eq]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul K, smul_smul]
  congr 1
  have hfac : (m.val.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

/-- The same coefficient written using the actual canonical-coordinate graph integrals. -/
theorem canonicalOneVertexCoefficient_eq_toCochain (m : Fin 4)
    (F : Multiderivation K (MvPolynomial (Fin d) K) m.val) :
    (∑ σ : Equiv.Perm (Fin m.val),
      algebraMap ℝ K (canonicalWeight (oneVertexGraph m.val σ) (oneVertex_edgeCount m.val)) •
        (oneVertexGraph m.val σ).cochainOperator
          (fun _ ↦ MixedGraphTaylorCoefficients.coordinateTensor m.val F)) =
      Multiderivation.toCochain F := by
  simp only [canonicalWeight_oneVertex]
  exact geometricOneVertexCoefficient_eq_toCochain m F

/-- The verified arity-three one-vertex sum is one sixth of raw alternating evaluation. -/
theorem geometricOneVertexCoefficient_three
    (F : Multiderivation K (MvPolynomial (Fin d) K) 3) :
    geometricOneVertexCoefficient ⟨3, by decide⟩ F =
      (1 / 6 : K) • F.val.toMultilinearMap := by
  rw [geometricOneVertexCoefficient_eq_toCochain]
  change (Nat.factorial 3 : K)⁻¹ • F.val.toMultilinearMap = _
  congr 1
  norm_num

theorem ofBinary_forward : KontsevichGraph.General.ofBinary Kontsevich.forwardGraph =
    oneVertexGraph 2 (1 : Equiv.Perm (Fin 2)) := Graph.ext rfl

theorem ofBinary_reverse : KontsevichGraph.General.ofBinary Kontsevich.reverseGraph =
    oneVertexGraph 2 (Equiv.swap 0 1) := Graph.ext rfl

omit [CharZero K] [Algebra ℝ K] in
/-- The forward graph is the raw bracket of every polynomial bivector. -/
theorem graphCoefficient_forward (F : Multiderivation K (MvPolynomial (Fin d) K) 2) :
    GraphTaylorCoefficients.graphCoefficient Kontsevich.forwardGraph (fun _ ↦ F) = rawBivector F := by
  apply (cochainTwoEquiv K (MvPolynomial (Fin d) K)).symm.injective
  rw [GraphTaylorCoefficients.graphCoefficient_apply, LinearEquiv.symm_apply_apply,
    rawBivector, LinearEquiv.symm_apply_apply, ofBinary_forward]
  apply MultilinearMap.ext
  intro f
  exact oneVertex_raw (1 : Equiv.Perm (Fin 2)) F f

omit [CharZero K] [Algebra ℝ K] in
/-- Reversing the outgoing order negates every actual polynomial bivector. -/
theorem graphCoefficient_reverse (F : Multiderivation K (MvPolynomial (Fin d) K) 2) :
    GraphTaylorCoefficients.graphCoefficient Kontsevich.reverseGraph (fun _ ↦ F) = -rawBivector F := by
  apply (cochainTwoEquiv K (MvPolynomial (Fin d) K)).symm.injective
  rw [GraphTaylorCoefficients.graphCoefficient_apply, LinearEquiv.symm_apply_apply,
    map_neg, rawBivector, LinearEquiv.symm_apply_apply, ofBinary_reverse]
  apply MultilinearMap.ext
  intro f
  change (oneVertexGraph 2 (Equiv.swap 0 1)).cochainOperator
    (fun _ ↦ MixedGraphTaylorCoefficients.coordinateTensor 2 F) f = -F f
  rw [oneVertex_raw]
  have h := F.val.map_perm f (Equiv.swap (0 : Fin 2) 1)
  simp only [Equiv.Perm.sign_swap (by decide : (0 : Fin 2) ≠ 1), Units.neg_smul, one_smul] at h
  convert h using 1
  rfl

/-- The actual geometric first graph coefficient is half the raw bivector on
all polynomial inputs, without a linear-coefficient restriction. -/
theorem weightedCoefficient_oneVertex (F : Multiderivation K (MvPolynomial (Fin d) K) 2) :
    GraphTaylorCoefficients.weightedCoefficient Finset.univ
      (fun Γ ↦ algebraMap ℝ K (Kontsevich.geometricOneVertexGraphWeight Γ)) (fun _ ↦ F) =
        (1 / 2 : K) • rawBivector F := by
  classical
  rw [GraphTaylorCoefficients.weightedCoefficient_apply, Kontsevich.oneVertex_graph_univ,
    Finset.sum_pair Kontsevich.forwardGraph_ne_reverseGraph,
    graphCoefficient_forward, graphCoefficient_reverse,
    Kontsevich.geometricOneVertexGraphWeight_forward,
    Kontsevich.geometricOneVertexGraphWeight_reverse]
  simp only [map_div₀, map_neg, map_one, map_ofNat, neg_div, neg_smul, smul_neg, neg_neg]
  rw [← add_smul]
  congr 1
  norm_num

/-- The genuine effective MC family inherits this normalization at arity one. -/
theorem effectiveFamily_one
    (s : (j : ℕ) → Finset (KontsevichGraph (j + 1)))
    (w : (j : ℕ) → KontsevichGraph (j + 1) → K)
    (hs : s 0 = Finset.univ)
    (hw : ∀ Γ, w 0 Γ = algebraMap ℝ K (Kontsevich.geometricOneVertexGraphWeight Γ))
    (F : Multiderivation K (MvPolynomial (Fin d) K) 2) :
    GraphTaylorCoefficients.effectiveFamily s w 1 (fun _ ↦ F) = (1 / 2 : K) • rawBivector F := by
  change GraphTaylorCoefficients.weightedCoefficient (s 0) (w 0) (fun _ ↦ F) = _
  rw [hs, funext hw]
  exact weightedCoefficient_oneVertex F

end Geometric

namespace Velocity

abbrev G := MixedGraphTaylorCoefficients.Graph 1 0

/-- The unique one-vertex graph for a distinguished vector field. -/
def graph : G where
  target _ := Sum.inr 0
  noLoops := by intros; simp
  distinctTargets v := by
    rw [Fin.eq_zero v]
    intro a b _
    exact @Subsingleton.elim (Fin 1) inferInstance a b

theorem edge_eq (e : Edge (MixedGraphTaylorCoefficients.arities 1 0)) : e = ⟨0, (0 : Fin 1)⟩ := by
  rcases e with ⟨v, a⟩
  rcases Fin.eq_zero v with rfl
  have ha : a = (0 : Fin 1) := Fin.eq_zero a
  subst a
  rfl

theorem graph_unique (Γ : G) : Γ = graph := by
  apply Graph.ext
  funext e
  rw [edge_eq e]
  have hn := Γ.noLoops 0 (0 : Fin 1)
  rcases ht : Γ.target ⟨0, (0 : Fin 1)⟩ with v | j
  · exact (hn (by rw [ht, Fin.eq_zero v])).elim
  · rw [Fin.eq_zero j]
    rfl

@[simp] theorem incoming_internal (v : Fin 1) : graph.incoming (Sum.inl v) = ∅ := by
  classical
  ext e
  simp [Graph.incoming, graph]

@[simp] theorem incoming_external (j : Fin 1) : graph.incoming (Sum.inr j) = {⟨0, (0 : Fin 1)⟩} := by
  classical
  ext e
  rw [edge_eq e, Fin.eq_zero j]
  simp [Graph.incoming, graph]

def labelEquiv (d : ℕ) : (Edge (MixedGraphTaylorCoefficients.arities 1 0) → Fin d) ≃ Fin d where
  toFun lab := lab ⟨0, (0 : Fin 1)⟩
  invFun i _ := i
  left_inv lab := by funext e; rw [edge_eq e]
  right_inv _ := rfl

/-- Direct coordinate contraction for the actual mixed-family graph type. -/
theorem graphCoefficient_apply (D : Multiderivation k (MvPolynomial (Fin d) k) 1)
    (f : Fin 1 → MvPolynomial (Fin d) k) :
    MixedGraphTaylorCoefficients.graphCoefficient graph Fin.elim0 D f =
      ∑ i : Fin d, D (fun _ ↦ X i) * pderiv i (f 0) := by
  classical
  letI : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))
  rw [MixedGraphTaylorCoefficients.graphCoefficient_apply, Graph.cochainOperator_apply]
  simp only [Graph.vertexDerivative, incoming_internal, incoming_external,
    Finset.toList_empty, List.map_nil, iteratedPDeriv, LinearMap.id_apply,
    Fin.prod_univ_one, Finset.toList_singleton, List.map_singleton,
    LinearMap.coe_comp, Function.comp_apply]
  apply Fintype.sum_equiv (labelEquiv d)
  intro lab
  congr 1
  rw [Fintype.prod_unique]
  change D (fun i : Fin 1 ↦ X (lab ⟨0, i⟩)) = D (fun _ ↦ X (lab ⟨0, (0 : Fin 1)⟩))
  congr 1
  funext i
  rw [Fin.eq_zero i]

/-- The unique mixed velocity graph is raw unary evaluation on every polynomial input. -/
theorem graphCoefficient_eq_raw (D : Multiderivation k (MvPolynomial (Fin d) k) 1) :
    MixedGraphTaylorCoefficients.graphCoefficient graph Fin.elim0 D = D.val.toMultilinearMap := by
  classical
  apply MultilinearMap.ext
  intro f
  rw [graphCoefficient_apply]
  change (∑ i : Fin d, D (fun _ ↦ X i) * pderiv i (f 0)) = D f
  rw [Multiderivation.apply_coordinate_expansion 1 D f]
  apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin d)).symm
  intro i
  simp only [Fin.prod_univ_one]
  rfl

/-- The native unary cochain and the native derivation agree for an actual vector field. -/
theorem cochainOne_raw (D : Multiderivation k (MvPolynomial (Fin d) k) 1) :
    cochainOneEquiv k (MvPolynomial (Fin d) k) D.val.toMultilinearMap =
      (Multiderivation.oneEquiv D).toLinearMap := by
  apply (cochainOneEquiv k (MvPolynomial (Fin d) k)).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  apply MultilinearMap.ext
  intro f
  rw [cochainOneEquiv_symm_apply]
  change D f = D (Function.update (fun _ ↦ 0) 0 (f 0))
  congr 1
  funext i
  rw [Fin.eq_zero i, Function.update_self]

theorem edgeCount : ∑ v : Fin (0 + 1), MixedGraphTaylorCoefficients.arities 1 0 v =
    Kontsevich.GraphForms.dimension 0 1 := by
  change (∑ v : Fin 1, MixedGraphTaylorCoefficients.arities 1 0 v) = _
  rw [Fin.sum_univ_one]
  rfl

theorem orderedEdges_eq_canonical
    (order : Fin (Kontsevich.GraphForms.dimension 0 1) ≃ Edge (MixedGraphTaylorCoefficients.arities 1 0)) :
    orderedEdges graph order = canonicalOneVertexEdges 1 := by
  funext a
  simp only [orderedEdges, graph, canonicalOneVertexEdges]
  rw [Fin.eq_zero (order a).1, Fin.eq_zero ((zeroIndex 1).symm a)]

/-- The native canonical graph integral agrees with the true labelled unary weight. -/
theorem canonicalWeight_eq_labelled (Γ : G) :
    canonicalWeight Γ edgeCount =
      Kontsevich.labelledOneVertexWeight ⟨1, by decide⟩ (1 : Equiv.Perm (Fin 1)) := by
  rw [graph_unique Γ, canonicalWeight, geometricWeight, orderedEdges_eq_canonical,
    rawIntegral_canonical_oneVertex ⟨1, by decide⟩,
    Kontsevich.labelledOneVertexWeight_eq, Kontsevich.canonicalOneVertexWeight]
  change (∏ v : Fin 1, ((MixedGraphTaylorCoefficients.arities 1 0 v).factorial : ℝ)⁻¹) *
    ((2 * Real.pi) ^ Kontsevich.GraphForms.dimension 0 1)⁻¹ * Kontsevich.oneVertexRawIntegral ⟨1, by decide⟩ = _
  simp [MixedGraphTaylorCoefficients.arities, Kontsevich.GraphForms.dimension]

section Geometric

variable {K : Type*} [Field K] [CharZero K] [Algebra ℝ K]

omit [CharZero K] in
/-- The actual one-vertex integral weight for the unique vector-field graph. -/
def weight (_Γ : G) : K :=
  algebraMap ℝ K (Kontsevich.labelledOneVertexWeight ⟨1, by decide⟩ (1 : Equiv.Perm (Fin 1)))

omit [CharZero K] in
@[simp] theorem weight_eq_one (Γ : G) : weight (K := K) Γ = 1 := by
  simp [weight, Kontsevich.labelledOneVertexWeight_eq, Kontsevich.canonicalOneVertexWeight_eq]

omit [CharZero K] in
/-- The weight used in the actual mixed family is precisely its native graph integral. -/
theorem weight_eq_canonical (Γ : G) :
    weight (K := K) Γ = algebraMap ℝ K (canonicalWeight Γ edgeCount) := by
  rw [canonicalWeight_eq_labelled]
  rfl

omit [CharZero K] in
/-- The genuine mixed one-vertex coefficient is exactly the native derivation. -/
theorem weightedCoefficient_oneVertex (D : Multiderivation K (MvPolynomial (Fin d) K) 1) :
    cochainOneEquiv K (MvPolynomial (Fin d) K)
      (MixedGraphTaylorCoefficients.weightedCoefficient Finset.univ weight Fin.elim0 D) =
        (Multiderivation.oneEquiv D).toLinearMap := by
  classical
  letI : Unique G := ⟨⟨graph⟩, graph_unique⟩
  rw [MixedGraphTaylorCoefficients.weightedCoefficient_apply, Fintype.sum_unique,
    weight_eq_one, one_smul]
  rw [show (default : G) = graph from rfl, graphCoefficient_eq_raw, cochainOne_raw]

omit [CharZero K] in
/-- At zero other vertices the actual velocity family has the required base map. -/
theorem velocityFamily_zero
    (s : (n : ℕ) → Finset (MixedGraphTaylorCoefficients.Graph 1 n))
    (w : (n : ℕ) → MixedGraphTaylorCoefficients.Graph 1 n → K)
    (hs : s 0 = Finset.univ) (hw : ∀ Γ, w 0 Γ = weight Γ)
    (D : Multiderivation K (MvPolynomial (Fin d) K) 1) :
    MixedGraphTaylorCoefficients.velocityFamily s w 0 Fin.elim0 D =
      (Multiderivation.oneEquiv D).toLinearMap := by
  change cochainOneEquiv K (MvPolynomial (Fin d) K)
    (MixedGraphTaylorCoefficients.weightedCoefficient (s 0) (w 0) Fin.elim0 D) = _
  rw [hs, funext hw]
  exact weightedCoefficient_oneVertex D

end Geometric

end Velocity

end EnvelopingIsomorphism.Deformation.Gauge.GraphFirstCoefficient
