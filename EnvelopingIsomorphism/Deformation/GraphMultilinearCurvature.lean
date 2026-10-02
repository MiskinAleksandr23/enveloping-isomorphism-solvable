import EnvelopingIsomorphism.Deformation.SymmetrizedGraphProfiles
import EnvelopingIsomorphism.FormalSeries.LaurentGroupedMultilinear

/-! The genuine independent-input source curvature bridge. The bracket is
inserted into the retained quotient vertex, and all other ordered bivectors
are kept separately. No diagonal specialization or polarization premise is used. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000

namespace EnvelopingIsomorphism.Deformation.GraphMultilinearCurvature

open scoped BigOperators Classical
open KontsevichGraph.General KontsevichGraph.General.TwoVertexContraction
open UniformBinaryGraphs UniformCurvatureSplits GraphWeightedInsertion
open GraphCoefficientProfiles GraphCurvatureProfiles SymmetrizedGraphProfiles
open SchoutenGraphContraction

variable {k : Type*} [Field k] [CharZero k] {n d : ℕ}

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

/-- The quotient graph's increasing complement reads the corresponding old
vertices of the expanded graph, with no assumption that the bivectors coincide. -/
def outsideInputs (i : Fin (n + 1)) (R : Fin (n + 2) → Bivector (k := k) (d := d)) :
    Fin n → Bivector (k := k) (d := d) :=
  fun j ↦ R (vertexSplitOldEmbedding i (placementEquiv i (Sum.inl j)))

def outsideTensors (i : Fin (n + 1)) (R : Fin (n + 2) → Bivector (k := k) (d := d))
    (v : Fin (n + 1)) : Tensor (Gauge.PlacedMixedGraphTaylorCoefficients.arities 3 i v) d k :=
  if h : v = i then 0 else tensorCast
    (show 2 = Gauge.PlacedMixedGraphTaylorCoefficients.arities 3 i v from (if_neg h).symm)
    (rawTensor (R (vertexSplitOldEmbedding i v)))

omit [CharZero k] in
private theorem tensorCast_heq {a b : ℕ} (h : a = b) (T : Tensor a d k) :
    HEq (tensorCast h T) T := by
  cases h
  rfl

omit [CharZero k] in
private theorem cast_tensor_map_apply {A : Type*} [AddCommGroup A] [Module k A]
    {a b : ℕ} (h : a = b) (f : A →ₗ[k] Tensor a d k) (x : A) :
    (cast (congrArg (fun r ↦ A →ₗ[k] Tensor r d k) h) f) x = tensorCast h (f x) := by
  cases h
  rfl

omit [CharZero k] in
/-- The actual placed coefficient with arbitrary ordered outside bivectors is
the graph operator with precisely one updated tensor. -/
theorem graphCoefficient_eq_update (i : Fin (n + 1)) (Θ : CurvatureGraph i)
    (R : Fin (n + 2) → Bivector (k := k) (d := d))
    (Q : Multiderivation k (MvPolynomial (Fin d) k) 3) :
    Gauge.PlacedMixedGraphTaylorCoefficients.graphCoefficient i Θ (outsideInputs i R) Q =
      Θ.cochainOperator (Function.update (outsideTensors i R) i
        (tensorCast (selectedArity i) (rawTensor Q))) := by
  rw [Gauge.PlacedMixedGraphTaylorCoefficients.graphCoefficient_apply]
  congr 1
  funext v
  have ho (s : Fin n ⊕ Fin 1) :
      Gauge.PlacedMixedGraphTaylorCoefficients.orderedInput i (outsideInputs i R) Q
        (placementEquiv i s) =
      Sum.elim (fun j ↦ (0, outsideInputs i R j)) (fun _ : Fin 1 ↦ (Q, 0)) s := by
    unfold Gauge.PlacedMixedGraphTaylorCoefficients.orderedInput
    exact congrArg _ ((placementEquiv i).symm_apply_apply s)
  by_cases hv : v = i
  · subst v
    have hr := ho (Sum.inr 0)
    rw [placementEquiv_inr] at hr
    rw [hr]
    simp only [Sum.elim_inr, Function.update_self,
      Gauge.PlacedMixedGraphTaylorCoefficients.vertexTensor]
    exact cast_tensor_map_apply
      (A := Gauge.PlacedMixedGraphTaylorCoefficients.PairInput k d 3) (selectedArity i)
      ((Gauge.MixedGraphTaylorCoefficients.coordinateTensor (k := k) (d := d) 3).comp
        (LinearMap.fst k _ _)) (Q, 0)
  · obtain ⟨s, hs⟩ := (placementEquiv i).surjective v
    cases s with
    | inl j =>
      have hr := ho (Sum.inl j)
      rw [hs] at hr
      rw [hr]
      simp only [Sum.elim_inl, Function.update_of_ne hv, outsideTensors, dif_neg hv,
        Gauge.PlacedMixedGraphTaylorCoefficients.vertexTensor]
      have hcast := cast_tensor_map_apply
        (A := Gauge.PlacedMixedGraphTaylorCoefficients.PairInput k d 3)
        (show 2 = Gauge.PlacedMixedGraphTaylorCoefficients.arities 3 i v from (if_neg hv).symm)
        ((Gauge.MixedGraphTaylorCoefficients.coordinateTensor (k := k) (d := d) 2).comp
          (LinearMap.snd k _ _)) (0, outsideInputs i R j)
      exact hcast.trans (congrArg (tensorCast _) (congrArg rawTensor
        (congrArg R (congrArg (vertexSplitOldEmbedding i) hs))))
    | inr j => exact (hv (hs.symm.trans (placementEquiv_inr i j))).elim

omit [CharZero k] in
/-- Outside tensors and the two independent children recover exactly the
original independently varying family on every expanded vertex. -/
theorem uniformSplitTensors_independent (i : Fin (n + 1))
    (R : Fin (n + 2) → Bivector (k := k) (d := d)) :
    uniformSplitTensors i (outsideTensors i R)
      (bivectorPairTensors (R (vertexSplitChild i 0)) (R (vertexSplitChild i 1))) =
      fun v ↦ Gauge.GraphTaylorCoefficients.coordinateTensor (R v) := by
  funext v
  obtain ⟨s, rfl⟩ := (vertexSplitSourceEquiv i).symm.surjective v
  cases s with
  | inl v =>
    rw [vertexSplitSourceEquiv_symm_old]
    apply eq_of_heq
    refine (uniformSplitTensors_old_heq i _ _ v.val v.property).trans ?_
    rw [outsideTensors, dif_neg v.property]
    exact tensorCast_heq _ _
  | inr c =>
    rw [vertexSplitSourceEquiv_symm_child, uniformSplitTensors_child]
    fin_cases c <;> rfl

omit [CharZero k] in
private theorem forward_independent (i : Fin (n + 1)) (Θ : CurvatureGraph i)
    (c : Fin 3) (χ : SplitChoices i Θ)
    (R : Fin (n + 2) → Bivector (k := k) (d := d)) :
    operator (uniformCurvatureForward i Θ c χ) R =
      (Θ.vertexSplit (bivectorForward (cyclicPermutation c)) i (selectedArity i).symm χ).cochainOperator
        (vertexSplitTensors (Gauge.PlacedMixedGraphTaylorCoefficients.arities 3 i) bivectorArity i
          (outsideTensors i R)
          (bivectorPairTensors (R (vertexSplitChild i 0)) (R (vertexSplitChild i 1)))) := by
  rw [operator_apply, ← uniformSplitTensors_independent i R]
  exact uniformCurvatureForward_cochainOperator i Θ c χ _ _

omit [CharZero k] in
private theorem reverse_independent (i : Fin (n + 1)) (Θ : CurvatureGraph i)
    (c : Fin 3) (χ : SplitChoices i Θ)
    (R : Fin (n + 2) → Bivector (k := k) (d := d)) :
    operator (uniformCurvatureReverse i Θ c χ) R =
      (Θ.vertexSplit (bivectorReverse (cyclicPermutation c)) i (selectedArity i).symm χ).cochainOperator
        (vertexSplitTensors (Gauge.PlacedMixedGraphTaylorCoefficients.arities 3 i) bivectorArity i
          (outsideTensors i R)
          (bivectorPairTensors (R (vertexSplitChild i 0)) (R (vertexSplitChild i 1)))) := by
  rw [operator_apply, ← uniformSplitTensors_independent i R]
  exact uniformCurvatureReverse_cochainOperator i Θ c χ _ _

/-- Exact six-template Schouten splitting with two independent child bivectors
and every surviving vertex retaining its own input. -/
theorem graphCoefficient_bracket_independent (i : Fin (n + 1)) (Θ : CurvatureGraph i)
    (R : Fin (n + 2) → Bivector (k := k) (d := d)) :
    Gauge.PlacedMixedGraphTaylorCoefficients.graphCoefficient i Θ (outsideInputs i R)
      (schoutenBracket k d 1 1 (R (vertexSplitChild i 0)) (R (vertexSplitChild i 1))) =
      ∑ c : Fin 3, ∑ χ : SplitChoices i Θ,
        (operator (uniformCurvatureForward i Θ c χ) R +
          operator (uniformCurvatureReverse i Θ c χ) R) := by
  rw [graphCoefficient_eq_update]
  apply MultilinearMap.ext
  intro f
  rw [cochainOperator_bivector_bracket_vertexSplit]
  simp only [sum_apply, add_apply, Finset.sum_add_distrib,
    forward_independent, reverse_independent]

/-- The actual source quotient graph with its two selected child inputs. -/
def quotientBracketValue (i : Fin (n + 1)) (Θ : CurvatureGraph i)
    (R : Fin (n + 2) → Bivector (k := k) (d := d)) : Ternary k (MvPolynomial (Fin d) k) :=
  cochainThreeEquiv k _
    (Gauge.PlacedMixedGraphTaylorCoefficients.graphCoefficient i Θ (outsideInputs i R)
      (schoutenBracket k d 1 1 (R (vertexSplitChild i 0)) (R (vertexSplitChild i 1))))

/-- The pure six-term scalar profile evaluates to the genuine source bracket
insertion on independent inputs before any symmetrization. -/
theorem evaluation_splitProfile_ordered (i : Fin (n + 1)) (Θ : CurvatureGraph i)
    (R : Fin (n + 2) → Bivector (k := k) (d := d)) :
    evaluation (ternaryMap (k := k) (d := d)) (splitProfile (k := k) i Θ) R =
      quotientBracketValue i Θ R := by
  simp only [splitProfile, map_sum, map_add, evaluation_pushforward, one_smul,
    sum_apply, add_apply, quotientBracketValue, Finset.sum_add_distrib]
  have h := congrArg (cochainThreeEquiv k (MvPolynomial (Fin d) k))
    (graphCoefficient_bracket_independent i Θ R)
  simp only [map_sum, map_add, Finset.sum_add_distrib] at h
  exact h.symm

/-- The actual source-side bracket insertion bundled as a multilinear map.
Multilinearity is transported from its proved independent-input graph expansion. -/
def quotientBracketMap (i : Fin (n + 1)) (Θ : CurvatureGraph i) : ProfileMap k d (n + 2) :=
  MultilinearMap.mk' (quotientBracketValue i Θ)
    (by
      intro R j x y
      simp only [← evaluation_splitProfile_ordered]
      exact (evaluation (ternaryMap (k := k) (d := d)) (splitProfile (k := k) i Θ)).map_update_add _ _ _ _)
    (by
      intro R j r x
      simp only [← evaluation_splitProfile_ordered]
      exact (evaluation (ternaryMap (k := k) (d := d)) (splitProfile (k := k) i Θ)).map_update_smul _ _ _ _)

@[simp] theorem quotientBracketMap_apply (i : Fin (n + 1)) (Θ : CurvatureGraph i)
    (R : Fin (n + 2) → Bivector (k := k) (d := d)) :
    quotientBracketMap i Θ R = quotientBracketValue i Θ R := rfl

theorem evaluation_splitProfile_map (i : Fin (n + 1)) (Θ : CurvatureGraph i) :
    evaluation (ternaryMap (k := k) (d := d)) (splitProfile (k := k) i Θ) = quotientBracketMap i Θ := by
  apply MultilinearMap.ext
  exact evaluation_splitProfile_ordered i Θ

/-- Full map equality, with every independently varying input symmetrized. -/
theorem evaluation_symmetrized_splitProfile (i : Fin (n + 1)) (Θ : CurvatureGraph i) :
    evaluation (symmetrizedValue (k := k) (d := d)) (splitProfile (k := k) i Θ) =
      symmetrize (quotientBracketMap i Θ) := by
  rw [← evaluation_splitProfile_map]
  simp only [evaluation_apply, map_sum, map_smul, symmetrizedValue]

/-- The actual weighted source quotient maps, including all retained positions
and the curvature factor one half. -/
def orderedCurvatureMap (w : (i : Fin (n + 1)) → CurvatureGraph i → k) : ProfileMap k d (n + 2) :=
  (1/2 : k) • ∑ i : Fin (n + 1), ∑ Θ : CurvatureGraph i, w i Θ • quotientBracketMap i Θ

theorem evaluation_curvatureProfile_map (w : (i : Fin (n + 1)) → CurvatureGraph i → k) :
    evaluation (ternaryMap (k := k) (d := d)) (curvatureProfile w) = orderedCurvatureMap w := by
  simp only [curvatureProfile, map_smul, map_sum, evaluation_splitProfile_map, orderedCurvatureMap]

/-- Exact non-diagonal curvature identity consumed by formal multilinear
convolution: no polynomial diagonal or assumed cochain identity intervenes. -/
theorem evaluation_symmetrized_curvatureProfile
    (w : (i : Fin (n + 1)) → CurvatureGraph i → k) :
    evaluation (symmetrizedValue (k := k) (d := d)) (curvatureProfile w) =
      symmetrize (orderedCurvatureMap w) := by
  simp only [curvatureProfile, map_smul, map_sum, evaluation_symmetrized_splitProfile,
    orderedCurvatureMap]

/-- Increasing complement enumeration, as an actual equivalence of vertex indices. -/
def outsideEquiv (i : Fin (n + 1)) : Fin n ≃ {v : Fin (n + 1) // v ≠ i} :=
  ((Gauge.PlacedMixedGraphTaylorCoefficients.bivectorSlots i).orderIsoOfFin
    (Gauge.PlacedMixedGraphTaylorCoefficients.card_bivectorSlots i)).toEquiv.trans
    (Equiv.subtypeEquivRight (fun v ↦ by
      simp [Gauge.PlacedMixedGraphTaylorCoefficients.bivectorSlots]))

@[simp] theorem outsideEquiv_val (i : Fin (n + 1)) (j : Fin n) :
    (outsideEquiv i j).val = placementEquiv i (Sum.inl j) := rfl

/-- The real input permutation moving the quotient complement to the first
n positions and its two split children to the final two positions. -/
def inputPermutation (i : Fin (n + 1)) : Equiv.Perm (Fin (n + 2)) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr (outsideEquiv i) (Equiv.refl (Fin 2))).trans (vertexSplitSourceEquiv i).symm)

@[simp] theorem inputPermutation_castAdd (i : Fin (n + 1)) (j : Fin n) :
    inputPermutation i (Fin.castAdd 2 j) =
      vertexSplitOldEmbedding i (placementEquiv i (Sum.inl j)) := by
  change (vertexSplitSourceEquiv i).symm
    ((Equiv.sumCongr (outsideEquiv i) (Equiv.refl (Fin 2)))
      (finSumFinEquiv.symm (Fin.castAdd 2 j))) = _
  rw [← finSumFinEquiv_apply_left, Equiv.symm_apply_apply]
  rfl

@[simp] theorem inputPermutation_natAdd (i : Fin (n + 1)) (c : Fin 2) :
    inputPermutation i (Fin.natAdd n c) = vertexSplitChild i c := by
  change (vertexSplitSourceEquiv i).symm
    ((Equiv.sumCongr (outsideEquiv i) (Equiv.refl (Fin 2)))
      (finSumFinEquiv.symm (Fin.natAdd n c))) = _
  rw [← finSumFinEquiv_apply_right, Equiv.symm_apply_apply]
  rfl

abbrev Trivector := Multiderivation k (MvPolynomial (Fin d) k) 3

/-- The actual Schouten bracket is a two-input multilinear map. -/
def bracketMap : MultilinearMap k (fun _ : Fin 2 ↦ Bivector (k := k) (d := d))
    (Trivector (k := k) (d := d)) :=
  MultilinearMap.mk' (fun R ↦ schoutenBracket k d 1 1 (R 0) (R 1))
    (by
      intro R j x y
      fin_cases j
      · change schoutenBracket k d 1 1 (x+y) (R 1) = _
        exact congrArg (fun F ↦ F (R 1)) ((schoutenBracket k d 1 1).map_add x y)
      · change schoutenBracket k d 1 1 (R 0) (x+y) = _
        exact (schoutenBracket k d 1 1 (R 0)).map_add x y)
    (by
      intro R j r x
      fin_cases j
      · change schoutenBracket k d 1 1 (r • x) (R 1) = _
        exact congrArg (fun F ↦ F (R 1)) ((schoutenBracket k d 1 1).map_smul r x)
      · change schoutenBracket k d 1 1 (R 0) (r • x) = _
        exact (schoutenBracket k d 1 1 (R 0)).map_smul r x)

/-- A quotient graph first reads n independent bivectors, then the bracket of
two further independent bivectors. This is the source composition used by MC. -/
def groupedQuotientMap (i : Fin (n + 1)) (Θ : CurvatureGraph i) : ProfileMap k d (n + 2) :=
  let C := (LinearMap.llcomp k _ _ _
    (cochainThreeEquiv k (MvPolynomial (Fin d) k)).toLinearMap).compMultilinearMap
      (Gauge.PlacedMixedGraphTaylorCoefficients.graphCoefficient i Θ)
  let post : (Trivector (k := k) (d := d) →ₗ[k] Ternary k (MvPolynomial (Fin d) k)) →ₗ[k]
      MultilinearMap k (fun _ : Fin 2 ↦ Bivector (k := k) (d := d))
        (Ternary k (MvPolynomial (Fin d) k)) :=
    { toFun H := H.compMultilinearMap bracketMap
      map_add' H J := by apply MultilinearMap.ext; intro R; rfl
      map_smul' r H := by apply MultilinearMap.ext; intro R; rfl }
  (post.compMultilinearMap C).uncurrySum.domDomCongr finSumFinEquiv

@[simp] theorem groupedQuotientMap_apply (i : Fin (n + 1)) (Θ : CurvatureGraph i)
    (R : Fin (n + 2) → Bivector (k := k) (d := d)) :
    groupedQuotientMap i Θ R = cochainThreeEquiv k _
      (Gauge.PlacedMixedGraphTaylorCoefficients.graphCoefficient i Θ
        (fun j ↦ R (Fin.castAdd 2 j))
        (schoutenBracket k d 1 1 (R (Fin.natAdd n 0)) (R (Fin.natAdd n 1)))) := rfl

/-- The ordered split input convention differs from the standard disjoint
groups by the proved concrete vertex permutation, with no weight assumption. -/
theorem quotientBracketMap_eq_grouped (i : Fin (n + 1)) (Θ : CurvatureGraph i) :
    quotientBracketMap (k := k) (d := d) i Θ =
      (groupedQuotientMap i Θ).domDomCongr (inputPermutation i) := by
  apply MultilinearMap.ext
  intro R
  change quotientBracketValue i Θ R = groupedQuotientMap i Θ (R ∘ inputPermutation i)
  rw [groupedQuotientMap_apply]
  apply congrArg (cochainThreeEquiv k (MvPolynomial (Fin d) k))
  apply congrArg₂ (fun F Q ↦ Gauge.PlacedMixedGraphTaylorCoefficients.graphCoefficient i Θ F Q)
  · funext j
    exact (congrArg R (inputPermutation_castAdd i j)).symm
  · exact congrArg₂ (fun F G ↦ schoutenBracket k d 1 1 F G)
      (congrArg R (inputPermutation_natAdd i 0)).symm
      (congrArg R (inputPermutation_natAdd i 1)).symm

theorem evaluation_symmetrized_splitProfile_grouped (i : Fin (n + 1)) (Θ : CurvatureGraph i) :
    evaluation (symmetrizedValue (k := k) (d := d)) (splitProfile (k := k) i Θ) =
      symmetrize (groupedQuotientMap i Θ) := by
  rw [evaluation_symmetrized_splitProfile, quotientBracketMap_eq_grouped, symmetrize_domDomCongr]

/-- Standard source-side grouping: n background inputs followed by two bracket
inputs, all retained, with the curvature normalization exactly one half. -/
def groupedCurvatureMap (w : (i : Fin (n + 1)) → CurvatureGraph i → k) : ProfileMap k d (n + 2) :=
  (1/2 : k) • ∑ i : Fin (n + 1), ∑ Θ : CurvatureGraph i, w i Θ • groupedQuotientMap i Θ

/-- The symmetrized scalar profile is exactly the symmetrized independent
source bracket composition, in the standard first-n/last-two grouping. -/
theorem evaluation_symmetrized_curvatureProfile_grouped
    (w : (i : Fin (n + 1)) → CurvatureGraph i → k) :
    evaluation (symmetrizedValue (k := k) (d := d)) (curvatureProfile w) =
      symmetrize (groupedCurvatureMap w) := by
  simp only [curvatureProfile, map_smul, map_sum, evaluation_symmetrized_splitProfile_grouped,
    groupedCurvatureMap]

/-- The source composition is literally the existing all-position placed
curvature Taylor family, on independent background arguments and a bracket pair. -/
theorem groupedCurvatureMap_eq_curvatureFamily
    (w : (j : ℕ) → (i : Fin (j + 1)) → CurvatureGraph i → k)
    (R : Fin (n + 2) → Bivector (k := k) (d := d)) :
    groupedCurvatureMap (w n) R =
      Gauge.PlacedMixedGraphTaylorCoefficients.curvatureFamily (fun _ _ ↦ Finset.univ) w n
        (fun j ↦ R (Fin.castAdd 2 j))
        ((1/2 : k) • (show Trivector (k := k) (d := d) from
          schoutenBracket k d 1 1 (R (Fin.natAdd n 0)) (R (Fin.natAdd n 1)))) := by
  simp only [groupedCurvatureMap, smul_apply, sum_apply, groupedQuotientMap_apply,
    Gauge.PlacedMixedGraphTaylorCoefficients.curvatureFamily,
    Gauge.PlacedMixedGraphTaylorCoefficients.mapOutput,
    LinearMap.compMultilinearMap_apply, LinearMap.llcomp_apply,
    Gauge.PlacedMixedGraphTaylorCoefficients.effectiveFamily_apply,
    map_smul, map_sum, Finset.smul_sum, smul_smul, mul_comm]
  rfl

/-- Scalar boundary equality now yields the correct independent multilinear
associator-to-source identity, suitable for actual Laurent convolution. -/
theorem boundaryRelation_source_multilinear
    {w : (j : ℕ) → BinaryGraph j 2 → k}
    {v : (j : ℕ) → (i : Fin (j + 1)) → CurvatureGraph i → k}
    (h : GraphBoundaryProfiles.ScalarBoundaryRelation w v) (n : ℕ) :
    evaluation (symmetrizedValue (k := k) (d := d))
      (GraphAssociatorProfiles.associatorProfile (n + 2) w) =
      symmetrize (groupedCurvatureMap (v n)) := by
  rw [boundaryRelation_multilinear h, evaluation_symmetrized_curvatureProfile_grouped]

open EnvelopingIsomorphism.FormalSeries

/-- The independent source map is the generic disjoint-group composition,
with the actual all-position curvature coefficient as its first operation. -/
theorem groupedCurvatureMap_eq_groupedBilinear
    (w : (j : ℕ) → (i : Fin (j + 1)) → CurvatureGraph i → k) :
    groupedCurvatureMap (k := k) (d := d) (w n) =
      LaurentModule.groupedBilinear LinearMap.id
        (Gauge.PlacedMixedGraphTaylorCoefficients.curvatureFamily (fun _ _ ↦ Finset.univ) w n)
        ((1/2 : k) • bracketMap) := by
  apply MultilinearMap.ext
  intro R
  rw [groupedCurvatureMap_eq_curvatureFamily, LaurentModule.groupedBilinear_apply]
  rfl

/-- The genuine Laurent bracket is exactly the convolution of the two-input
polynomial Schouten map. This keeps arbitrary negative powers of the inputs. -/
theorem applyMultilinear_bracketMap
    (ζ η : LaurentModule k (Bivector (k := k) (d := d))) :
    LaurentModule.applyMultilinear bracketMap ![ζ, η] =
      LaurentModule.extendBilinear (schoutenBracket k d 1 1) ζ η := by
  apply LaurentModule.ext
  intro e
  rfl

/-- Actual bounded Laurent extension of the independent source composition,
with no restriction to polynomial inputs over a Laurent scalar field. -/
theorem applyMultilinear_groupedCurvatureMap
    (w : (j : ℕ) → (i : Fin (j + 1)) → CurvatureGraph i → k)
    (ζ : LaurentModule k (Bivector (k := k) (d := d))) :
    LaurentModule.applyMultilinear (groupedCurvatureMap (w n)) (fun _ ↦ ζ) =
      LaurentModule.extendBilinear LinearMap.id
        (LaurentModule.applyMultilinear
          (Gauge.PlacedMixedGraphTaylorCoefficients.curvatureFamily (fun _ _ ↦ Finset.univ) w n)
          (fun _ ↦ ζ))
        ((1/2 : k) • LaurentModule.extendBilinear (schoutenBracket k d 1 1) ζ ζ) := by
  rw [groupedCurvatureMap_eq_groupedBilinear, LaurentModule.applyMultilinear_groupedBilinear_diagonal]
  have hsmul := (LaurentModule.applyMultilinearLinear (fun _ : Fin 2 ↦ ζ)).map_smul (1/2 : k)
    (bracketMap (k := k) (d := d))
  change LaurentModule.applyMultilinear ((1/2 : k) • bracketMap) (fun _ ↦ ζ) =
    (1/2 : k) • LaurentModule.applyMultilinear bracketMap (fun _ ↦ ζ) at hsmul
  rw [hsmul]
  congr 2

/-- Every source curvature coefficient vanishes on an actual Laurent
Poisson input, after the independent-input composition has been transferred. -/
theorem applyMultilinear_groupedCurvatureMap_eq_zero
    (w : (j : ℕ) → (i : Fin (j + 1)) → CurvatureGraph i → k)
    (ζ : LaurentModule k (Bivector (k := k) (d := d)))
    (hζ : LaurentModule.extendBilinear (schoutenBracket k d 1 1) ζ ζ = 0) :
    LaurentModule.applyMultilinear (groupedCurvatureMap (w n)) (fun _ ↦ ζ) = 0 := by
  rw [applyMultilinear_groupedCurvatureMap, hζ, smul_zero, map_zero]

end EnvelopingIsomorphism.Deformation.GraphMultilinearCurvature
