import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFaceLabelRelabelling
import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointActualFaceIntegral
import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFaceNonzeroAdmissibility
import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFaceEdgeOrderRelabelling

/-! Actual product face integrals under internal vertex relabelling. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointFaceRelabelling
open InteriorGraphFaceCoordinates InteriorFaceLabelRelabelling Set MeasureTheory
open scoped Classical
variable {n m : ℕ} (σ : Equiv.Perm (Fin n)) {S T : Finset (Fin n)}
  (hST : ∀ j, σ j ∈ T ↔ j ∈ S) {i a b : Fin n}

include hST in
theorem shapeDegree_eq : shapeDegree (σ a) (σ b) T = shapeDegree a b S :=
  congrArg (fun N => InteriorFiberAngleSplit.Dim N + 1) (shapeN_eq σ hST)

include hST in
theorem coarseDegree_eq : coarseDegree (σ i) (σ a) T m = coarseDegree i a S m :=
  congrArg (fun N => GraphForms.dimension N m) (coarseN_eq σ hST)

include hST in
theorem degree_eq : shapeDegree (σ a) (σ b) T + coarseDegree (σ i) (σ a) T m =
    shapeDegree a b S + coarseDegree i a S m :=
  congrArg₂ Nat.add (shapeDegree_eq σ hST) (coarseDegree_eq σ hST)

def edges (es : Fin (shapeDegree a b S + coarseDegree i a S m) → Edge n m) :
    Fin (shapeDegree (σ a) (σ b) T + coarseDegree (σ i) (σ a) T m) → Edge n m :=
  fun j => relabelEdge σ (es (finCongr (degree_eq σ hST) j))

theorem internal_edges (es : Fin (shapeDegree a b S + coarseDegree i a S m) → Edge n m)
    (j : Fin (shapeDegree (σ a) (σ b) T + coarseDegree (σ i) (σ a) T m)) :
    IsInternal T (edges σ hST es j) ↔ IsInternal S (es (finCongr (degree_eq σ hST) j)) :=
  isInternal_relabel σ hST _

theorem nonloop_edges (es : Fin (shapeDegree a b S + coarseDegree i a S m) → Edge n m)
    (hne : ∀ j, (es j).2 ≠ Sum.inl (es j).1)
    (j : Fin (shapeDegree (σ a) (σ b) T + coarseDegree (σ i) (σ a) T m)) :
    (edges σ hST es j).2 ≠ Sum.inl (edges σ hST es j).1 := by
  let q := finCongr (degree_eq σ hST) j
  change Sum.map σ id (es q).2 ≠ Sum.inl (σ (es q).1)
  intro h
  apply hne q
  rcases ht : (es q).2 with t | t
  · rw [ht, Sum.map_inl, Sum.inl.injEq] at h
    exact congrArg Sum.inl (σ.injective h)
  · simp [ht] at h

theorem internalCount_edges
    (es : Fin (shapeDegree a b S + coarseDegree i a S m) → Edge n m) :
    Fintype.card {j // IsInternal T (edges σ hST es j)} =
      Fintype.card {j // IsInternal S (es j)} :=
  Fintype.card_congr ((finCongr (degree_eq σ hST)).subtypeEquiv (internal_edges σ hST es))

theorem internal_count
    (es : Fin (shapeDegree a b S + coarseDegree i a S m) → Edge n m)
    (hc : Fintype.card {j // IsInternal S (es j)} = shapeDegree a b S) :
    Fintype.card {j // IsInternal T (edges σ hST es j)} = shapeDegree (σ a) (σ b) T := by
  rw [internalCount_edges, hc, shapeDegree_eq σ hST]

include hST in
theorem card_eq : T.card = S.card := by
  have he : S.map σ.toEmbedding = T := by
    ext j
    obtain ⟨k,rfl⟩ := σ.surjective j
    simp [hST]
  rw [← he, Finset.card_map]

def integral (es : Fin (shapeDegree a b S + coarseDegree i a S m) → Edge n m) : ℝ :=
  ∫ x in InteriorFiberAngleSplit.integrationRegion (shapeN a b S) ×ˢ
    GeometricWeights.realDomain (coarseN i a S) m, realFaceDensity es x

theorem density_permute
    (es : Fin (shapeDegree a b S + coarseDegree i a S m) → Edge n m)
    (τ : Equiv.Perm (Fin (shapeDegree a b S + coarseDegree i a S m)))
    (x : RealProductCoordinates i a b S m) :
    realFaceDensity (fun j => es (τ j)) x = (τ.sign : ℝ) * realFaceDensity es x := by
  unfold realFaceDensity graphForm
  change GraphFormProduct.ofCovectors (fun j => edgeLinear (es (τ j)) (toAngularReal x))
    (fun j => fderiv ℝ toAngularReal x (faceFrame j)) = (τ.sign : ℝ) *
      GraphFormProduct.ofCovectors (fun j => edgeLinear (es j) (toAngularReal x))
        (fun j => fderiv ℝ toAngularReal x (faceFrame j))
  simpa only [Equiv.refl_apply, Equiv.Perm.sign_refl, Int.cast_one, Units.val_one, mul_one]
    using GraphFormProduct.ofCovectors_permuted_apply
      (fun j => edgeLinear (es j) (toAngularReal x))
      (fun j => fderiv ℝ toAngularReal x (faceFrame j)) τ (Equiv.refl _)

theorem integral_permute
    (es : Fin (shapeDegree a b S + coarseDegree i a S m) → Edge n m)
    (τ : Equiv.Perm (Fin (shapeDegree a b S + coarseDegree i a S m))) :
    integral (fun j => es (τ j)) = (τ.sign : ℝ) * integral es := by
  unfold integral
  simp only [density_permute, integral_const_mul]

theorem integral_zero_of_count_ne_one
    (es : Fin (shapeDegree a b S + coarseDegree i a S m) → Edge n m)
    (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hS : S.card = 2)
    (hne : ∀ j, (es j).2 ≠ Sum.inl (es j).1)
    (hc : Fintype.card {j // IsInternal S (es j)} ≠ 1) : integral es = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro x hx
  by_contra hz
  exact hc (InteriorFaceNonzeroAdmissibility.internal_count_eq_one_of_density_ne_zero
    es x ha hb hba hS hx hne hz)

theorem integral_eq_factor
    (es : Fin (shapeDegree a b S + coarseDegree i a S m) → Edge n m)
    (hc : Fintype.card {j // IsInternal S (es j)} = shapeDegree a b S)
    (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hS : S.card = 2)
    (hne : ∀ j, (es j).2 ≠ Sum.inl (es j).1) :
    integral es = (Equiv.Perm.sign (edgeBlockPermutation es hc).symm : ℝ) *
      ((2 * Real.pi) * GeometricWeights.rawIntegral (coarseEdges es hc)) :=
  (TwoPointActualFaceIntegral.integral_realFaceDensity es hc ha hb hba hS hne).2

theorem rawIntegral_coarse_relabel
    (es : Fin (shapeDegree a b S + coarseDegree i a S m) → Edge n m)
    (hc : Fintype.card {j // IsInternal S (es j)} = shapeDegree a b S) :
    GeometricWeights.rawIntegral
      (coarseEdges (edges σ hST es) (internal_count σ hST es hc)) =
        GeometricWeights.rawIntegral (coarseEdges es hc) := by
  apply rawIntegral_between (coarseN_eq σ hST) (coarseLabelEquiv σ hST)
  intro j
  have hindex := InteriorFaceEdgeOrderRelabelling.externalIndex_transport
    es (edges σ hST es) (shapeDegree_eq σ hST) (coarseDegree_eq σ hST)
    (degree_eq σ hST) (internal_edges σ hST es) hc (internal_count σ hST es hc) j
  unfold coarseEdges
  change coarseEdge (relabelEdge σ (es (finCongr (degree_eq σ hST)
      (externalIndex (edges σ hST es) (internal_count σ hST es hc) j)))) = _
  rw [← hindex]
  exact coarseEdge_relabel σ hST _

/-- The literal product-face integral is unchanged by internal labels, with
the anchor and two shape marks transported. All native row signs are derived. -/
theorem integral_edges
    (es : Fin (shapeDegree a b S + coarseDegree i a S m) → Edge n m)
    (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hS : S.card = 2)
    (hne : ∀ j, (es j).2 ≠ Sum.inl (es j).1) :
    integral (edges σ hST es) = integral es := by
  have ha' := (hST a).mpr ha
  have hb' := (hST b).mpr hb
  have hba' := σ.injective.ne hba
  have hT : T.card = 2 := (card_eq σ hST).trans hS
  have hne' := nonloop_edges σ hST es hne
  by_cases hc : Fintype.card {j // IsInternal S (es j)} = 1
  · have hcount : Fintype.card {j // IsInternal S (es j)} = shapeDegree a b S := by
      exact hc.trans (by rw [InteriorGraphFaceCoordinates.shapeDegree_eq ha hb hba, hS])
    rw [integral_eq_factor _ (internal_count σ hST es hcount) ha' hb' hba' hT hne',
      integral_eq_factor es hcount ha hb hba hS hne,
      rawIntegral_coarse_relabel σ hST es hcount]
    simp only [Equiv.Perm.sign_symm]
    rw [InteriorFaceEdgeOrderRelabelling.edgeBlockPermutation_sign_transport
      es (edges σ hST es) (shapeDegree_eq σ hST) (coarseDegree_eq σ hST)
      (degree_eq σ hST) (internal_edges σ hST es) hcount (internal_count σ hST es hcount)]
  · rw [integral_zero_of_count_ne_one es ha hb hba hS hne hc,
      integral_zero_of_count_ne_one _ ha' hb' hba' hT hne']
    simpa only [internalCount_edges] using hc

end EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointFaceRelabelling
