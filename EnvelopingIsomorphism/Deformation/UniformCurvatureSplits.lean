import EnvelopingIsomorphism.Deformation.UniformBinaryGraphs
import EnvelopingIsomorphism.Deformation.SchoutenGraphVertexSplit
import EnvelopingIsomorphism.Deformation.Gauge.PlacedMixedGraphTaylorCoefficients

/-! The six actual Schouten vertex splits of a placed curvature graph become
uniform binary graphs. Raw signs and the curvature coefficient one-half remain explicit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace EnvelopingIsomorphism.Deformation.UniformCurvatureSplits
open KontsevichGraph.General KontsevichGraph.General.TwoVertexContraction
open SchoutenGraphContraction UniformBinaryGraphs
open scoped BigOperators Classical


variable {n : ℕ} (i : Fin (n+1))

theorem selectedArity : 3 = Gauge.PlacedMixedGraphTaylorCoefficients.arities 3 i i := by simp [Gauge.PlacedMixedGraphTaylorCoefficients.arities]

theorem vertexSplitArity_two :
    vertexSplitArity (Gauge.PlacedMixedGraphTaylorCoefficients.arities 3 i) bivectorArity i = fun _ : Fin (n+2) ↦ 2 := by
  funext v
  obtain ⟨s, rfl⟩ := (vertexSplitSourceEquiv i).symm.surjective v
  cases s with
  | inl v => simp [vertexSplitArity, Gauge.PlacedMixedGraphTaylorCoefficients.arities, v.property]
  | inr c => simp [vertexSplitArity]

/-- Every incoming arrow of the original curvature vertex makes its actual
choice between the two consecutive children. -/
abbrev SplitChoices (Θ : Gauge.PlacedMixedGraphTaylorCoefficients.Graph 3 i) := Θ.VertexSplitChoices i

def uniformCurvatureForward (Θ : Gauge.PlacedMixedGraphTaylorCoefficients.Graph 3 i) (c : Fin 3) (χ : SplitChoices i Θ) :
    BinaryGraph (n+2) 3 :=
  castGraph (vertexSplitArity_two i)
    (Θ.vertexSplit (bivectorForward (cyclicPermutation c)) i (selectedArity i).symm χ)

def uniformCurvatureReverse (Θ : Gauge.PlacedMixedGraphTaylorCoefficients.Graph 3 i) (c : Fin 3) (χ : SplitChoices i Θ) :
    BinaryGraph (n+2) 3 :=
  castGraph (vertexSplitArity_two i)
    (Θ.vertexSplit (bivectorReverse (cyclicPermutation c)) i (selectedArity i).symm χ)

variable {K : Type*} [Field K] [CharZero K] {d : ℕ}

/-- Only nonselected vertices of the background are used after splitting. -/
def backgroundTensors (π : Multiderivation K (MvPolynomial (Fin d) K) 2)
    (v : Fin (n+1)) : Tensor (Gauge.PlacedMixedGraphTaylorCoefficients.arities 3 i v) d K :=
  if h : v = i then 0 else tensorCast (show 2 = Gauge.PlacedMixedGraphTaylorCoefficients.arities 3 i v from (if_neg h).symm) (rawTensor π)

omit [CharZero K] in
private theorem tensorCast_heq {p p' : ℕ} (h : p = p') (T : Tensor p d K) :
    HEq (tensorCast h T) T := by
  cases h
  rfl

omit [CharZero K] in
private theorem castTensors_heq {l : ℕ} {q q' : Fin l → ℕ} (h : q = q')
    (T : (v : Fin l) → Tensor (q v) d K) (v : Fin l) :
    HEq (castTensors h T v) (T v) := by
  cases h
  rfl

/-- General transported tensor data: unchanged outside tensors and arbitrary
ordered tensors at the two genuine split children. -/
def uniformSplitTensors
    (T : (v : Fin (n+1)) → Tensor (Gauge.PlacedMixedGraphTaylorCoefficients.arities 3 i v) d K)
    (U : Fin 2 → Tensor 2 d K) : Fin (n+2) → Tensor 2 d K :=
  castTensors (vertexSplitArity_two i)
    (vertexSplitTensors (Gauge.PlacedMixedGraphTaylorCoefficients.arities 3 i) bivectorArity i T U)

omit [CharZero K] in
theorem uniformSplitTensors_old_heq
    (T : (v : Fin (n+1)) → Tensor (Gauge.PlacedMixedGraphTaylorCoefficients.arities 3 i v) d K)
    (U : Fin 2 → Tensor 2 d K) (v : Fin (n+1)) (hv : v ≠ i) :
    HEq (uniformSplitTensors i T U (vertexSplitOldEmbedding i v)) (T v) :=
  (castTensors_heq (vertexSplitArity_two i) _ _).trans
    (vertexSplitTensors_old_heq _ _ _ T U v hv)

omit [CharZero K] in
theorem uniformSplitTensors_child
    (T : (v : Fin (n+1)) → Tensor (Gauge.PlacedMixedGraphTaylorCoefficients.arities 3 i v) d K)
    (U : Fin 2 → Tensor 2 d K) (c : Fin 2) :
    uniformSplitTensors i T U (vertexSplitChild i c) = U c :=
  eq_of_heq ((castTensors_heq (vertexSplitArity_two i) _ _).trans
    (vertexSplitTensors_child_heq _ _ _ T U c))

omit [CharZero K] in
theorem uniformCurvatureForward_cochainOperator
    (Θ : Gauge.PlacedMixedGraphTaylorCoefficients.Graph 3 i) (c : Fin 3) (χ : SplitChoices i Θ)
    (T : (v : Fin (n+1)) → Tensor (Gauge.PlacedMixedGraphTaylorCoefficients.arities 3 i v) d K)
    (U : Fin 2 → Tensor 2 d K) :
    (uniformCurvatureForward i Θ c χ).cochainOperator (uniformSplitTensors i T U) =
      (Θ.vertexSplit (bivectorForward (cyclicPermutation c)) i (selectedArity i).symm χ).cochainOperator
        (vertexSplitTensors (Gauge.PlacedMixedGraphTaylorCoefficients.arities 3 i) bivectorArity i T U) :=
  cochainOperator_castGraph (vertexSplitArity_two i) _ _

omit [CharZero K] in
theorem uniformCurvatureReverse_cochainOperator
    (Θ : Gauge.PlacedMixedGraphTaylorCoefficients.Graph 3 i) (c : Fin 3) (χ : SplitChoices i Θ)
    (T : (v : Fin (n+1)) → Tensor (Gauge.PlacedMixedGraphTaylorCoefficients.arities 3 i v) d K)
    (U : Fin 2 → Tensor 2 d K) :
    (uniformCurvatureReverse i Θ c χ).cochainOperator (uniformSplitTensors i T U) =
      (Θ.vertexSplit (bivectorReverse (cyclicPermutation c)) i (selectedArity i).symm χ).cochainOperator
        (vertexSplitTensors (Gauge.PlacedMixedGraphTaylorCoefficients.arities 3 i) bivectorArity i T U) :=
  cochainOperator_castGraph (vertexSplitArity_two i) _ _

omit [CharZero K] in
private theorem backgroundTensors_old_heq (π : Multiderivation K (MvPolynomial (Fin d) K) 2)
    (v : Fin (n+1)) (hv : v ≠ i) : HEq (backgroundTensors i π v) (rawTensor π) := by
  rw [backgroundTensors, dif_neg hv]
  exact tensorCast_heq _ _

omit [CharZero K] in
private theorem cast_tensor_map_apply {A : Type*} [AddCommGroup A] [Module K A]
    {p p' : ℕ} (h : p = p') (f : A →ₗ[K] Tensor p d K) (x : A) :
    (cast (congrArg (fun r ↦ A →ₗ[K] Tensor r d K) h) f) x = tensorCast h (f x) := by
  cases h
  rfl

omit [CharZero K] in
/-- The actual placed coefficient is a genuine tensor update at the selected
vertex; the remaining ordered vertices carry their actual raw bivectors. -/
theorem graphCoefficient_eq_update (Θ : Gauge.PlacedMixedGraphTaylorCoefficients.Graph 3 i)
    (π : Multiderivation K (MvPolynomial (Fin d) K) 2)
    (D : Multiderivation K (MvPolynomial (Fin d) K) 3) :
    Gauge.PlacedMixedGraphTaylorCoefficients.graphCoefficient i Θ (fun _ ↦ π) D =
      Θ.cochainOperator (Function.update (backgroundTensors i π) i
        (tensorCast (selectedArity i) (rawTensor D))) := by
  rw [Gauge.PlacedMixedGraphTaylorCoefficients.graphCoefficient_diagonal]
  congr 1
  funext v
  by_cases hv : v = i
  · subst v
    simp only [Function.update_self, Gauge.PlacedMixedGraphTaylorCoefficients.vertexTensor]
    exact cast_tensor_map_apply (A := Gauge.PlacedMixedGraphTaylorCoefficients.PairInput K d 3) (selectedArity i)
      ((Gauge.MixedGraphTaylorCoefficients.coordinateTensor (k := K) (d := d) 3).comp (LinearMap.fst K _ _)) (D,0)
  · simp only [if_neg hv, Function.update_of_ne hv, Gauge.PlacedMixedGraphTaylorCoefficients.vertexTensor,
      dif_neg hv, backgroundTensors]
    exact cast_tensor_map_apply (A := Gauge.PlacedMixedGraphTaylorCoefficients.PairInput K d 3) (show 2 = Gauge.PlacedMixedGraphTaylorCoefficients.arities 3 i v from (if_neg hv).symm)
      ((Gauge.MixedGraphTaylorCoefficients.coordinateTensor (k := K) (d := d) 2).comp (LinearMap.snd K _ _)) (0,π)

omit [CharZero K] in
/-- Once the selected vertex is removed, all surviving/child tensors are the
same raw polynomial bivector, including the two-vertex case n=0. -/
theorem splitTensors_constant (π : Multiderivation K (MvPolynomial (Fin d) K) 2) :
    castTensors (vertexSplitArity_two i)
      (vertexSplitTensors (Gauge.PlacedMixedGraphTaylorCoefficients.arities 3 i) bivectorArity i
        (backgroundTensors i π) (bivectorPairTensors π π)) =
      fun _ : Fin (n+2) ↦ Gauge.GraphTaylorCoefficients.coordinateTensor π := by
  funext v
  obtain ⟨s, rfl⟩ := (vertexSplitSourceEquiv i).symm.surjective v
  cases s with
  | inl v =>
    rw [vertexSplitSourceEquiv_symm_old]
    apply eq_of_heq
    exact (castTensors_heq _ _ _).trans
      ((vertexSplitTensors_old_heq _ _ _ _ _ v.val v.property).trans
        (backgroundTensors_old_heq i π v.val v.property))
  | inr c =>
    rw [vertexSplitSourceEquiv_symm_child]
    apply eq_of_heq
    have h := (castTensors_heq (vertexSplitArity_two i)
      (vertexSplitTensors (Gauge.PlacedMixedGraphTaylorCoefficients.arities 3 i) bivectorArity i
        (backgroundTensors i π) (bivectorPairTensors π π)) (vertexSplitChild i c)).trans
      (vertexSplitTensors_child_heq _ _ _ _ _ c)
    fin_cases c <;> exact h

/-- The genuine six-term raw Schouten contraction as uniform graph cochains. -/
theorem graphCoefficient_bracket (Θ : Gauge.PlacedMixedGraphTaylorCoefficients.Graph 3 i)
    (π : Multiderivation K (MvPolynomial (Fin d) K) 2) :
    Gauge.PlacedMixedGraphTaylorCoefficients.graphCoefficient i Θ (fun _ ↦ π) (schoutenBracket K d 1 1 π π) =
      ∑ c : Fin 3,
        ((∑ χ : SplitChoices i Θ, operator (uniformCurvatureForward i Θ c χ) (fun _ ↦ π)) +
          ∑ χ : SplitChoices i Θ, operator (uniformCurvatureReverse i Θ c χ) (fun _ ↦ π)) := by
  rw [graphCoefficient_eq_update]
  apply MultilinearMap.ext
  intro f
  rw [cochainOperator_bivector_bracket_vertexSplit]
  simp only [sum_apply, add_apply]
  apply Finset.sum_congr rfl
  intro c hc
  congr 1 <;> apply Finset.sum_congr rfl <;> intro χ hχ
  · rw [operator_apply, ← splitTensors_constant i π]
    exact congrArg (fun C ↦ C f) (cochainOperator_castGraph (vertexSplitArity_two i) _ _).symm
  · rw [operator_apply, ← splitTensors_constant i π]
    exact congrArg (fun C ↦ C f) (cochainOperator_castGraph (vertexSplitArity_two i) _ _).symm

/-- Curvature keeps the actual factor one-half and all three forward/reverse
pairs of graph templates. -/
theorem graphCoefficient_half_bracket (Θ : Gauge.PlacedMixedGraphTaylorCoefficients.Graph 3 i)
    (π : Multiderivation K (MvPolynomial (Fin d) K) 2) :
    Gauge.PlacedMixedGraphTaylorCoefficients.graphCoefficient i Θ (fun _ ↦ π) ((1/2 : K) • (show Multiderivation K (MvPolynomial (Fin d) K) 3 from schoutenBracket K d 1 1 π π)) =
      (1/2 : K) • ∑ c : Fin 3,
        ∑ χ : SplitChoices i Θ,
          (operator (uniformCurvatureForward i Θ c χ) (fun _ ↦ π) +
            operator (uniformCurvatureReverse i Θ c χ) (fun _ ↦ π)) := by
  rw [map_smul, graphCoefficient_bracket]
  simp only [Finset.sum_add_distrib]

/-- The optional Poisson specialization kills the explicit half-split sum. -/
theorem half_split_sum_eq_zero (Θ : Gauge.PlacedMixedGraphTaylorCoefficients.Graph 3 i)
    (π : Multiderivation K (MvPolynomial (Fin d) K) 2)
    (hπ : (show Multiderivation K (MvPolynomial (Fin d) K) 3 from schoutenBracket K d 1 1 π π) = 0) :
    (1/2 : K) • ∑ c : Fin 3, ∑ χ : SplitChoices i Θ,
      (operator (uniformCurvatureForward i Θ c χ) (fun _ ↦ π) +
        operator (uniformCurvatureReverse i Θ c χ) (fun _ ↦ π)) = 0 := by
  rw [← graphCoefficient_half_bracket, hπ, smul_zero, map_zero]

end EnvelopingIsomorphism.Deformation.UniformCurvatureSplits
