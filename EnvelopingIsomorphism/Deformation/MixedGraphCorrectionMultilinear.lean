import EnvelopingIsomorphism.Deformation.MixedGraphCorrectionProfiles
import EnvelopingIsomorphism.Deformation.GraphMultilinearCurvature

/-! Independent-input and grouped multilinear evaluation of the signed two-odd correction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000

namespace EnvelopingIsomorphism.Deformation.MixedGraphCorrectionMultilinear

open KontsevichGraph.General MixedGraphProfileCarrier MixedGraphCorrectionProfiles
open SchoutenGraphContraction GraphCoefficientProfiles
open scoped BigOperators Classical

variable {n : ℕ}

abbrev Outside (p : Placement n) := {v : Fin (n + 2) // v ≠ p.1 ∧ v ≠ p.2.val}

def ordinarySlots (p : Placement n) : Finset (Fin (n + 2)) := {p.1, p.2.val}ᶜ

theorem card_ordinarySlots (p : Placement n) : (ordinarySlots p).card = n := by
  simp [ordinarySlots, Finset.card_compl, p.2.property.symm]

def outsideEquiv (p : Placement n) : Fin n ≃ Outside p :=
  ((ordinarySlots p).orderIsoOfFin (card_ordinarySlots p)).toEquiv.trans
    (Equiv.subtypeEquivRight (fun v => by simp [ordinarySlots]))

def sourceMap (p : Placement n) : Outside p ⊕ Fin 2 → Fin (n + 2) :=
  Sum.elim Subtype.val (Fin.cases p.1 (fun _ => p.2.val))

theorem sourceMap_bijective (p : Placement n) : Function.Bijective (sourceMap p) := by
  constructor
  · rintro (v | c) (w | d) h
    · exact congrArg Sum.inl (Subtype.ext h)
    · fin_cases d
      · exact (v.property.1 h).elim
      · exact (v.property.2 h).elim
    · fin_cases c
      · exact (w.property.1 h.symm).elim
      · exact (w.property.2 h.symm).elim
    · fin_cases c <;> fin_cases d
      · rfl
      · exact (p.2.property h.symm).elim
      · exact (p.2.property h).elim
      · rfl
  · intro v
    by_cases hvi : v = p.1
    · exact ⟨Sum.inr 0, hvi.symm⟩
    · by_cases hvj : v = p.2.val
      · exact ⟨Sum.inr 1, hvj.symm⟩
      · exact ⟨Sum.inl ⟨v, hvi, hvj⟩, rfl⟩

def sourceEquiv (p : Placement n) : Fin (n + 2) ≃ Outside p ⊕ Fin 2 :=
  (Equiv.ofBijective (sourceMap p) (sourceMap_bijective p)).symm

def quotientPlacement (p : Placement n) : Fin n ⊕ Fin 2 ≃ Fin (n + 2) :=
  (Equiv.sumCongr (outsideEquiv p) (Equiv.refl _)).trans (sourceEquiv p).symm

@[simp] theorem quotientPlacement_inl (p : Placement n) (j : Fin n) :
    quotientPlacement p (Sum.inl j) = (outsideEquiv p j).val := rfl

@[simp] theorem quotientPlacement_vector (p : Placement n) : quotientPlacement p (Sum.inr 0) = p.1 := rfl
@[simp] theorem quotientPlacement_trivector (p : Placement n) : quotientPlacement p (Sum.inr 1) = p.2.val := rfl

variable {k : Type*} [Field k] [CharZero k] {d : ℕ}

abbrev Pack := Vector (k := k) (d := d) × Trivector (k := k) (d := d) × Bivector (k := k) (d := d)
abbrev C := Cochain k (MvPolynomial (Fin d) k) 2

def vectorPack : Vector (k := k) (d := d) →ₗ[k] (Pack (k := k) (d := d)) := LinearMap.inl k _ _
def trivectorPack : Trivector (k := k) (d := d) →ₗ[k] (Pack (k := k) (d := d)) :=
  (LinearMap.inr k _ _).comp (LinearMap.inl k _ _)
def binaryPack : Bivector (k := k) (d := d) →ₗ[k] (Pack (k := k) (d := d)) :=
  (LinearMap.inr k _ _).comp (LinearMap.inr k _ _)

def vertexPackTensor (p : Placement n) (v : Fin (n + 2)) :
    Pack (k := k) (d := d) →ₗ[k] Tensor (twoOddArity p.1 p.2 v) d k := by
  by_cases hvi : v = p.1
  · have hq : twoOddArity p.1 p.2 v = 1 := by simp [twoOddArity, hvi]
    rw [hq]
    exact (Gauge.MixedGraphTaylorCoefficients.coordinateTensor 1).comp (LinearMap.fst k _ _)
  · by_cases hvj : v = p.2.val
    · have hq : twoOddArity p.1 p.2 v = 3 := by simp [twoOddArity, hvj, p.2.property]
      rw [hq]
      exact (Gauge.MixedGraphTaylorCoefficients.coordinateTensor 3).comp
        ((LinearMap.fst k _ _).comp (LinearMap.snd k _ _))
    · have hq : twoOddArity p.1 p.2 v = 2 := by simp [twoOddArity, hvi, hvj]
      rw [hq]
      exact (Gauge.MixedGraphTaylorCoefficients.coordinateTensor 2).comp
        ((LinearMap.snd k _ _).comp (LinearMap.snd k _ _))

def packedCoefficient (p : Placement n) (Θ : QuotientGraph p) :
    MultilinearMap k (fun _ : Fin (n + 2) => Pack (k := k) (d := d)) (C (k := k) (d := d)) :=
  Θ.cochainOperator.compLinearMap (vertexPackTensor p)

def distinguishQ :
    MultilinearMap k (fun _ : Fin 1 => Pack (k := k) (d := d)) (C (k := k) (d := d)) →ₗ[k]
      (Trivector (k := k) (d := d) →ₗ[k] (C (k := k) (d := d))) :=
  (MultilinearMap.ofSubsingletonₗ k k _ _ (0 : Fin 1)).symm.toLinearMap.comp
    (MultilinearMap.compLinearMapₗ (fun _ : Fin 1 => trivectorPack))

def distinguishTwo :
    MultilinearMap k (fun _ : Fin 2 => Pack (k := k) (d := d)) (C (k := k) (d := d)) →ₗ[k]
      (Vector (k := k) (d := d) →ₗ[k] Trivector (k := k) (d := d) →ₗ[k] (C (k := k) (d := d))) where
  toFun H := (distinguishQ.comp H.curryLeft).comp vectorPack
  map_add' H J := by ext X Q; rfl
  map_smul' r H := by ext X Q; rfl

/-- A genuine multilinear quotient operator on n independent binary inputs,
linear independently in the fixed ordered arguments X and Q. -/
def quotientOperator (p : Placement n) (Θ : QuotientGraph p) :
    MultilinearMap k (fun _ : Fin n => Bivector (k := k) (d := d))
      (Vector (k := k) (d := d) →ₗ[k] Trivector (k := k) (d := d) →ₗ[k] (C (k := k) (d := d))) :=
  (distinguishTwo.compMultilinearMap
    ((packedCoefficient p Θ).domDomCongr (quotientPlacement p).symm).currySum).compLinearMap
      (fun _ => binaryPack)

omit [CharZero k] in
theorem quotientOperator_apply (p : Placement n) (Θ : QuotientGraph p)
    (B : Fin n → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d))
    (Q : Trivector (k := k) (d := d)) :
    quotientOperator p Θ B X Q = Θ.cochainOperator (fun v => vertexPackTensor p v
      (Sum.elim (fun j => (0, 0, B j))
        (Fin.cases (X, 0, 0) (fun _ => (0, Q, 0))) ((quotientPlacement p).symm v))) := rfl

def outsideInputs (p : Placement n) (B : Fin n → Bivector (k := k) (d := d)) (v : Fin (n + 2)) :
    Bivector (k := k) (d := d) :=
  if h : v ≠ p.1 ∧ v ≠ p.2.val then B ((outsideEquiv p).symm ⟨v, h⟩) else 0

omit [CharZero k] in
@[simp] theorem outsideInputs_equiv (p : Placement n) (B : Fin n → Bivector (k := k) (d := d))
    (j : Fin n) : outsideInputs p B (outsideEquiv p j).val = B j := by
  simp [outsideInputs, (outsideEquiv p j).property]

omit [CharZero k] in
private theorem cast_linear_apply_heq {A : Type*} [AddCommGroup A] [Module k A]
    {p q : ℕ} (h : p = q) (L : A →ₗ[k] Tensor p d k) (a : A) :
    HEq ((cast (congrArg (fun r => A →ₗ[k] Tensor r d k) h) L) a) (L a) := by
  cases h
  rfl

theorem vertexPackTensor_vector_heq (p : Placement n) (Z : Pack (k := k) (d := d)) :
    HEq (vertexPackTensor p p.1 Z) (rawTensor Z.1) := by
  simp only [vertexPackTensor, dite_true]
  exact cast_linear_apply_heq (by simp [twoOddArity]) _ _

theorem vertexPackTensor_trivector_heq (p : Placement n) (Z : Pack (k := k) (d := d)) :
    HEq (vertexPackTensor p p.2.val Z) (rawTensor Z.2.1) := by
  simp only [vertexPackTensor, dif_neg p.2.property, dite_true]
  exact cast_linear_apply_heq (by simp [twoOddArity, p.2.property]) _ _

theorem vertexPackTensor_binary_heq (p : Placement n) (v : Outside p) (Z : Pack (k := k) (d := d)) :
    HEq (vertexPackTensor p v.val Z) (rawTensor Z.2.2) := by
  simp only [vertexPackTensor, dif_neg v.property.1, dif_neg v.property.2]
  exact cast_linear_apply_heq (by simp [twoOddArity, v.property.1, v.property.2]) _ _

/-- The multilinear construction evaluates to the actual dependent tensors,
not to a postulated coefficient operation. -/
theorem quotientOperator_eq_value (p : Placement n) (Θ : QuotientGraph p)
    (B : Fin n → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d))
    (Q : Trivector (k := k) (d := d)) :
    quotientOperator p Θ B X Q = quotientValue p Θ (outsideInputs p B) X Q := by
  rw [quotientOperator_apply]
  apply congrArg Θ.cochainOperator
  funext v
  obtain ⟨s, rfl⟩ := (quotientPlacement p).surjective v
  rw [Equiv.symm_apply_apply]
  cases s with
  | inl j =>
    simp only [Sum.elim_inl, quotientPlacement_inl]
    apply eq_of_heq
    refine (vertexPackTensor_binary_heq p (outsideEquiv p j) _).trans ?_
    have h := twoOddTensors_binary_heq p.1 p.2 p.2.property (rawTensor X) (rawTensor Q)
      (fun v => rawTensor (outsideInputs p B v)) (outsideEquiv p j).val
      (outsideEquiv p j).property.1 (outsideEquiv p j).property.2
    simpa only [outsideInputs_equiv, quotientTensors] using h.symm
  | inr c =>
    fin_cases c
    · simp only [Sum.elim_inr]
      exact eq_of_heq ((vertexPackTensor_vector_heq p _).trans (twoOddTensors_vector_heq _ _ _ _ _ _).symm)
    · simp only [Sum.elim_inr]
      exact eq_of_heq ((vertexPackTensor_trivector_heq p _).trans (twoOddTensors_trivector_heq _ _ _ _ _ _).symm)

/-- The actual remaining expanded vertices are the old binary vertices and two children. -/
def expandedBinarySourceMap (p : Placement n) : Outside p ⊕ Fin 2 →
    {v : Fin (n + 3) // v ≠ expandedVector p}
  | Sum.inl w => ⟨vertexSplitOldEmbedding p.2 w.val,
      fun h => w.property.1 (splitExternalEmbedding_injective p.2.val h)⟩
  | Sum.inr c => ⟨vertexSplitChild p.2 c,
      (vertexSplitOld_ne_child p.2.val p.1 p.2.property.symm c).symm⟩

theorem expandedBinarySourceMap_bijective (p : Placement n) :
    Function.Bijective (expandedBinarySourceMap p) := by
  constructor
  · rintro (v | c) (w | d) h
    · exact congrArg Sum.inl (Subtype.ext (splitExternalEmbedding_injective p.2.val (congrArg Subtype.val h)))
    · exact (vertexSplitOld_ne_child p.2.val v.val v.property.2 d (congrArg Subtype.val h)).elim
    · exact (vertexSplitOld_ne_child p.2.val w.val w.property.2 c (congrArg Subtype.val h).symm).elim
    · exact congrArg Sum.inr (vertexSplitChild_injective p.2.val (congrArg Subtype.val h))
  · rintro ⟨v, hv⟩
    obtain ⟨s, rfl⟩ := (vertexSplitSourceEquiv p.2.val).symm.surjective v
    cases s with
    | inl w =>
      have hwi : w.val ≠ p.1 := by
        intro hw
        apply hv
        simp only [vertexSplitSourceEquiv_symm_old, expandedVector, hw]
      exact ⟨Sum.inl ⟨w.val, hwi, w.property⟩, rfl⟩
    | inr c => exact ⟨Sum.inr c, rfl⟩

def expandedBinarySourceEquiv (p : Placement n) : Outside p ⊕ Fin 2 ≃
    {v : Fin (n + 3) // v ≠ expandedVector p} :=
  Equiv.ofBijective _ (expandedBinarySourceMap_bijective p)

/-- An actual permutation of binary input slots: ordinary quotient inputs first,
then the two children, while the separately linear vector argument stays fixed. -/
def inputPermutation (p : Placement n) : Equiv.Perm (Fin (n + 2)) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr (outsideEquiv p) (Equiv.refl (Fin 2))).trans
    ((expandedBinarySourceEquiv p).trans (GraphMultilinearCurvature.outsideEquiv (expandedVector p)).symm))

theorem inputPermutation_old (p : Placement n) (j : Fin n) :
    placementEquiv (expandedVector p) (Sum.inl (inputPermutation p (Fin.castAdd 2 j))) =
      vertexSplitOldEmbedding p.2 (outsideEquiv p j).val := by
  change (GraphMultilinearCurvature.outsideEquiv (expandedVector p)
    (inputPermutation p (Fin.castAdd 2 j))).val = _
  unfold inputPermutation
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [← finSumFinEquiv_apply_left, Equiv.symm_apply_apply]
  rfl

theorem inputPermutation_child (p : Placement n) (c : Fin 2) :
    placementEquiv (expandedVector p) (Sum.inl (inputPermutation p (Fin.natAdd n c))) =
      vertexSplitChild p.2 c := by
  change (GraphMultilinearCurvature.outsideEquiv (expandedVector p)
    (inputPermutation p (Fin.natAdd n c))).val = _
  unfold inputPermutation
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [← finSumFinEquiv_apply_right, Equiv.symm_apply_apply]
  rfl

def liftBivectors {l : ℕ} (i : Fin (l + 1)) (R : Fin l → Bivector (k := k) (d := d))
    (v : Fin (l + 1)) : Bivector (k := k) (d := d) :=
  if h : v ≠ i then R ((GraphMultilinearCurvature.outsideEquiv i).symm ⟨v, h⟩) else 0

omit [CharZero k] in
@[simp] theorem liftBivectors_placement {l : ℕ} (i : Fin (l + 1))
    (R : Fin l → Bivector (k := k) (d := d)) (j : Fin l) :
    liftBivectors i R (placementEquiv i (Sum.inl j)) = R j := by
  change liftBivectors i R (GraphMultilinearCurvature.outsideEquiv i j).val = _
  rw [liftBivectors, dif_pos (GraphMultilinearCurvature.outsideEquiv i j).property]
  exact congrArg R ((GraphMultilinearCurvature.outsideEquiv i).symm_apply_apply j)

theorem liftBivectors_old (p : Placement n) (R : Fin (n + 2) → Bivector (k := k) (d := d))
    (j : Fin n) :
    liftBivectors (expandedVector p) R (vertexSplitOldEmbedding p.2 (outsideEquiv p j).val) =
      R (inputPermutation p (Fin.castAdd 2 j)) := by
  rw [← inputPermutation_old, liftBivectors_placement]

theorem liftBivectors_child (p : Placement n) (R : Fin (n + 2) → Bivector (k := k) (d := d))
    (c : Fin 2) :
    liftBivectors (expandedVector p) R (vertexSplitChild p.2 c) =
      R (inputPermutation p (Fin.natAdd n c)) := by
  rw [← inputPermutation_child, liftBivectors_placement]

theorem operator_eq_rawValue_lift {l m : ℕ} (Γ : VectorGraph l m)
    (R : Fin l → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    operator Γ R X = rawValue Γ (liftBivectors Γ.vertex R) X := by
  simpa only [liftBivectors_placement] using operator_eq_rawValue Γ (liftBivectors Γ.vertex R) X

omit [CharZero k] in
theorem quotientValue_congr_background (p : Placement n) (Θ : QuotientGraph p)
    (B E : Fin (n + 2) → Bivector (k := k) (d := d))
    (X : Vector (k := k) (d := d)) (Q : Trivector (k := k) (d := d))
    (h : ∀ v, v ≠ p.1 → v ≠ p.2.val → B v = E v) : quotientValue p Θ B X Q = quotientValue p Θ E X Q := by
  apply congrArg Θ.cochainOperator
  funext v
  by_cases hi : v = p.1
  · subst v
    exact eq_of_heq ((twoOddTensors_vector_heq _ _ _ _ _ _).trans (twoOddTensors_vector_heq _ _ _ _ _ _).symm)
  · by_cases hj : v = p.2.val
    · subst v
      exact eq_of_heq ((twoOddTensors_trivector_heq _ _ _ _ _ _).trans
        (twoOddTensors_trivector_heq _ _ _ _ _ _).symm)
    · apply eq_of_heq
      refine (twoOddTensors_binary_heq _ _ _ _ _ _ v hi hj).trans ?_
      rw [h v hi hj]
      exact (twoOddTensors_binary_heq p.1 p.2 p.2.property (rawTensor X) (rawTensor Q)
        (fun v => rawTensor (E v)) v hi hj).symm

abbrev ProfileMap (l : ℕ) := MultilinearMap k (fun _ : Fin l => Bivector (k := k) (d := d))
  (Vector (k := k) (d := d) →ₗ[k] C (k := k) (d := d))

def orderedQuotientMap (p : Placement n) (Θ : QuotientGraph p) : ProfileMap (k := k) (d := d) (n + 2) :=
  evaluation (operator (k := k) (d := d)) (splitProfile (k := k) p Θ)

theorem orderedQuotientMap_apply (p : Placement n) (Θ : QuotientGraph p)
    (R : Fin (n + 2) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    orderedQuotientMap p Θ R X =
      quotientValue p Θ (liftBivectors (expandedVector p) R ∘ vertexSplitOldEmbedding p.2) X
        (schoutenBracket k d 1 1 (liftBivectors (expandedVector p) R (vertexSplitChild p.2 0))
          (liftBivectors (expandedVector p) R (vertexSplitChild p.2 1))) := by
  rw [quotientValue_bracket]
  simp only [orderedQuotientMap, splitProfile, map_sum, map_add, evaluation_pushforward, one_smul,
    sum_apply, add_apply, LinearMap.sum_apply, LinearMap.add_apply, Finset.sum_add_distrib]
  apply congrArg₂ (fun A B : C (k := k) (d := d) => A + B)
  · apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro χ _
    exact operator_eq_rawValue_lift (splitForward p Θ c χ) R X
  · apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro χ _
    exact operator_eq_rawValue_lift (splitReverse p Θ c χ) R X

def groupedQuotientMap (p : Placement n) (Θ : QuotientGraph p) : ProfileMap (k := k) (d := d) (n + 2) :=
  let post : (Vector (k := k) (d := d) →ₗ[k] Trivector (k := k) (d := d) →ₗ[k] C (k := k) (d := d)) →ₗ[k]
      MultilinearMap k (fun _ : Fin 2 => Bivector (k := k) (d := d))
        (Vector (k := k) (d := d) →ₗ[k] C (k := k) (d := d)) :=
    { toFun H := H.flip.compMultilinearMap GraphMultilinearCurvature.bracketMap
      map_add' H J := by ext R X; rfl
      map_smul' r H := by ext R X; rfl }
  (post.compMultilinearMap (quotientOperator p Θ)).uncurrySum.domDomCongr finSumFinEquiv

@[simp] theorem groupedQuotientMap_apply (p : Placement n) (Θ : QuotientGraph p)
    (R : Fin (n + 2) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    groupedQuotientMap p Θ R X = quotientOperator p Θ (fun j => R (Fin.castAdd 2 j)) X
      (schoutenBracket k d 1 1 (R (Fin.natAdd n 0)) (R (Fin.natAdd n 1))) := rfl

/-- The true independent-input quotient bracket is the standard first-n/last-two
composition after the explicitly constructed permutation of its binary slots. -/
theorem orderedQuotientMap_eq_grouped (p : Placement n) (Θ : QuotientGraph p) :
    orderedQuotientMap (k := k) (d := d) p Θ = (groupedQuotientMap p Θ).domDomCongr (inputPermutation p) := by
  apply MultilinearMap.ext
  intro R
  apply LinearMap.ext
  intro X
  change orderedQuotientMap p Θ R X = groupedQuotientMap p Θ (R ∘ inputPermutation p) X
  rw [orderedQuotientMap_apply, groupedQuotientMap_apply, quotientOperator_eq_value,
    liftBivectors_child, liftBivectors_child]
  apply quotientValue_congr_background
  intro v hvi hvj
  obtain ⟨j, hj⟩ := (outsideEquiv p).surjective ⟨v, hvi, hvj⟩
  have hjv := congrArg Subtype.val hj
  change (outsideEquiv p j).val = v at hjv
  rw [← hjv, outsideInputs_equiv]
  exact liftBivectors_old p R j

def symmetrize {l : ℕ} : ProfileMap (k := k) (d := d) l →ₗ[k] ProfileMap (k := k) (d := d) l :=
  (l.factorial : k)⁻¹ • ∑ σ : Equiv.Perm (Fin l),
    (MultilinearMap.domDomCongrLinearEquiv k k (Bivector (k := k) (d := d))
      (Vector (k := k) (d := d) →ₗ[k] C (k := k) (d := d)) σ).toLinearMap

omit [CharZero k] in
theorem symmetrize_apply {l : ℕ} (F : ProfileMap (k := k) (d := d) l)
    (R : Fin l → Bivector (k := k) (d := d)) :
    symmetrize F R = (l.factorial : k)⁻¹ • ∑ σ : Equiv.Perm (Fin l), F (R ∘ σ) := by
  simp only [symmetrize, LinearMap.smul_apply, LinearMap.sum_apply, smul_apply, sum_apply]
  rfl

theorem symmetrize_domDomCongr {l : ℕ} (F : ProfileMap (k := k) (d := d) l) (τ : Equiv.Perm (Fin l)) :
    symmetrize (F.domDomCongr τ) = symmetrize F := by
  apply MultilinearMap.ext
  intro R
  rw [symmetrize_apply, symmetrize_apply]
  congr 1
  apply Fintype.sum_equiv (Equiv.mulRight τ)
  intro σ
  rfl

theorem evaluation_symmetrized_splitProfile_grouped (p : Placement n) (Θ : QuotientGraph p) :
    evaluation (fun Γ => symmetrize (operator (k := k) (d := d) Γ)) (splitProfile (k := k) p Θ) =
      symmetrize (groupedQuotientMap p Θ) := by
  rw [← symmetrize_domDomCongr _ (inputPermutation p), ← orderedQuotientMap_eq_grouped]
  simp only [orderedQuotientMap, evaluation_apply, map_sum, map_smul]

def groupedCorrectionMap (w : CorrectionGraph n → k) : ProfileMap (k := k) (d := d) (n + 2) :=
  (1 / 2 : k) • ∑ p : Placement n, ∑ Θ : QuotientGraph p,
    (placementSign p * w ⟨p, Θ⟩) • groupedQuotientMap p Θ

/-- Scalar correction evaluation is the actual symmetrized independent-input
bracket composition, with the two-odd sign and curvature one-half unchanged. -/
theorem evaluation_symmetrized_correctionProfile_grouped (w : CorrectionGraph n → k) :
    evaluation (fun Γ => symmetrize (operator (k := k) (d := d) Γ)) (correctionProfile w) =
      symmetrize (groupedCorrectionMap w) := by
  simp only [correctionProfile, map_smul, map_sum, evaluation_symmetrized_splitProfile_grouped,
    groupedCorrectionMap]

/-- The actual signed correction family is multilinear in ordinary bivectors
and independently linear in X and Q, before substituting any bracket. -/
def correctionFamily (w : CorrectionGraph n → k) :
    MultilinearMap k (fun _ : Fin n => Bivector (k := k) (d := d))
      (Vector (k := k) (d := d) →ₗ[k] Trivector (k := k) (d := d) →ₗ[k] C (k := k) (d := d)) :=
  ∑ p : Placement n, ∑ Θ : QuotientGraph p, (placementSign p * w ⟨p, Θ⟩) • quotientOperator p Θ

theorem groupedCorrectionMap_apply_family (w : CorrectionGraph n → k)
    (R : Fin (n + 2) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    groupedCorrectionMap w R X = correctionFamily w (fun j => R (Fin.castAdd 2 j)) X
      ((1 / 2 : k) • (show Trivector (k := k) (d := d) from
        schoutenBracket k d 1 1 (R (Fin.natAdd n 0)) (R (Fin.natAdd n 1)))) := by
  simp only [groupedCorrectionMap, correctionFamily, smul_apply, sum_apply,
    LinearMap.smul_apply, LinearMap.sum_apply, groupedQuotientMap_apply, map_smul,
    Finset.smul_sum, smul_smul]

def correctionFamilyFlip (w : CorrectionGraph n → k) :
    MultilinearMap k (fun _ : Fin n => Bivector (k := k) (d := d))
      (Trivector (k := k) (d := d) →ₗ[k] Vector (k := k) (d := d) →ₗ[k] C (k := k) (d := d)) :=
  let flip : (Vector (k := k) (d := d) →ₗ[k] Trivector (k := k) (d := d) →ₗ[k] C (k := k) (d := d)) →ₗ[k]
      (Trivector (k := k) (d := d) →ₗ[k] Vector (k := k) (d := d) →ₗ[k] C (k := k) (d := d)) :=
    { toFun H := H.flip
      map_add' H J := by ext Q X; rfl
      map_smul' r H := by ext Q X; rfl }
  flip.compMultilinearMap (correctionFamily w)

open EnvelopingIsomorphism.FormalSeries

/-- The grouped correction is the genuine disjoint-input composition, suitable
for actual Laurent coefficient convolution without a polynomial-diagonal inference. -/
theorem groupedCorrectionMap_eq_groupedBilinear (w : CorrectionGraph n → k) :
    groupedCorrectionMap (k := k) (d := d) w = LaurentModule.groupedBilinear LinearMap.id
      (correctionFamilyFlip w) ((1 / 2 : k) • GraphMultilinearCurvature.bracketMap) := by
  apply MultilinearMap.ext
  intro R
  apply LinearMap.ext
  intro X
  rw [groupedCorrectionMap_apply_family, LaurentModule.groupedBilinear_apply]
  rfl

theorem applyMultilinear_groupedCorrectionMap (w : CorrectionGraph n → k)
    (ζ : LaurentModule k (Bivector (k := k) (d := d))) :
    LaurentModule.applyMultilinear (groupedCorrectionMap w) (fun _ => ζ) =
      LaurentModule.extendBilinear LinearMap.id
        (LaurentModule.applyMultilinear (correctionFamilyFlip w) (fun _ => ζ))
        ((1 / 2 : k) • LaurentModule.extendBilinear (schoutenBracket k d 1 1) ζ ζ) := by
  rw [groupedCorrectionMap_eq_groupedBilinear, LaurentModule.applyMultilinear_groupedBilinear_diagonal]
  have h := (LaurentModule.applyMultilinearLinear (fun _ : Fin 2 => ζ)).map_smul (1 / 2 : k)
    (GraphMultilinearCurvature.bracketMap (k := k) (d := d))
  change LaurentModule.applyMultilinear ((1 / 2 : k) • GraphMultilinearCurvature.bracketMap) (fun _ => ζ) =
    (1 / 2 : k) • LaurentModule.applyMultilinear GraphMultilinearCurvature.bracketMap (fun _ => ζ) at h
  rw [h]
  congr 2

/-- The full Laurent source curvature annihilates the correction as a linear
operator on the still-independent vector argument. Negative Laurent powers are retained. -/
theorem applyMultilinear_groupedCorrectionMap_eq_zero (w : CorrectionGraph n → k)
    (ζ : LaurentModule k (Bivector (k := k) (d := d)))
    (hζ : LaurentModule.extendBilinear (schoutenBracket k d 1 1) ζ ζ = 0) :
    LaurentModule.applyMultilinear (groupedCorrectionMap (d := d) w) (fun _ => ζ) = 0 := by
  rw [applyMultilinear_groupedCorrectionMap, hζ, smul_zero, map_zero]

end EnvelopingIsomorphism.Deformation.MixedGraphCorrectionMultilinear
