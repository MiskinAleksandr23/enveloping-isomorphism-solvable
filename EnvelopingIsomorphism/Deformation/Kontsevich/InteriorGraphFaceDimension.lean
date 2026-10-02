import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorGraphFaceDomain
import EnvelopingIsomorphism.Deformation.Kontsevich.GraphFormProductDimension

/-! Dimension exclusion for the actual interior face graph form. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.InteriorGraphFaceCoordinates
open InteriorFiberAngleSplit GraphFormProduct ContinuousAlternatingMap
open scoped Classical
variable {n m : ℕ} {i a b : Fin n} {S : Finset (Fin n)}

abbrev shapeDegree (a b : Fin n) (S : Finset (Fin n)) := Dim (shapeN a b S) + 1
abbrev coarseDegree (i a : Fin n) (S : Finset (Fin n)) (m : ℕ) := GraphForms.dimension (coarseN i a S) m

theorem finrank_shape : Module.finrank ℝ (ShapeCoordinates a b S) = shapeDegree a b S := by
  simp [ShapeCoordinates, Parameters, Shape, Module.finrank_prod, Module.finrank_pi_fintype,
    Complex.finrank_real_complex, shapeDegree, Dim, AngularRadial.realDimension, Nat.add_comm]

theorem finrank_coarse : Module.finrank ℝ (CoarseCoordinates i a S m) = coarseDegree i a S m := by
  simp [CoarseCoordinates, GraphForms.Coordinates, Module.finrank_prod, Module.finrank_pi_fintype,
    Complex.finrank_real_complex, coarseDegree]

theorem cluster_card_ge_two (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) : 2 ≤ S.card := by
  have hsub : ({a, b} : Finset (Fin n)) ⊆ S := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl <;> assumption
  have h := Finset.card_le_card hsub
  simpa [Finset.card_pair hba.symm] using h

/-- The number of angular directions is the literal 2|S|−3. -/
theorem shapeDegree_eq (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) :
    shapeDegree a b S = 2 * S.card - 3 := by
  have h := cluster_card_ge_two ha hb hba
  simp only [shapeDegree, Dim, AngularRadial.realDimension, shapeN,
    card_clusterShapeIndex a b S ha hb hba]
  omega

theorem totalDegree_eq (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hanchor : i ∈ S → a = i) :
    shapeDegree a b S + coarseDegree i a S m = 2 * n + m - 3 := by
  have hs := cluster_card_ge_two ha hb hba
  have hle : S.card ≤ n := by simpa using Finset.card_le_card (Finset.subset_univ S)
  rw [shapeDegree_eq ha hb hba]
  simp only [coarseDegree, GraphForms.dimension, coarseN, card_clusterCoarseIndex i a S ha hanchor]
  omega

/-- Every wrong internal edge count annihilates the whole actual graph pullback. -/
theorem graphForm_eq_zero_of_dimension_mismatch {r s : ℕ}
    (edges : Fin (r + s) → Edge n m)
    (hcount : Fintype.card {q // IsInternal S (edges q)} = r)
    (hba : b ≠ a) (x : ProductCoordinates i a b S m)
    (hx : (toAngular x).toFree.OpenConditions) (hne : ∀ q, (edges q).2 ≠ Sum.inl (edges q).1)
    (htotal : r + s = shapeDegree a b S + coarseDegree i a S m)
    (hr : r ≠ shapeDegree a b S) :
    (graphForm edges (toAngular x)).compContinuousLinearMap (fderiv ℝ toAngular x) = 0 := by
  let α := planarCovectors (a := a) (b := b) edges hcount x.1
  let β := fun j ↦ GraphForms.edgeLinear (coarseEdges (i := i) edges hcount j) x.2
  have hz : ofCovectors (productCovectors α β) = 0 :=
    form_product_eq_zero_of_dimension_mismatch α β (by simpa only [finrank_shape, finrank_coarse] using htotal)
      (by simpa only [finrank_shape] using hr)
  have heq (q : Fin (r + s)) : faceCovector (edges q) x =
      productCovectors α β ((edgeBlockPermutation edges hcount).symm q) := by
    have hh := faceCovector_block edges hcount hba x hx hne ((edgeBlockPermutation edges hcount).symm q)
    simpa [α, β] using hh
  ext v
  change ofCovectors (fun q ↦ faceCovector (edges q) x) v = 0
  simp_rw [heq]
  have hh := ofCovectors_permuted_apply (productCovectors α β) v
    (edgeBlockPermutation edges hcount).symm (Equiv.refl _)
  simpa [hz] using hh

/-- The exact numerical exclusion at the original ambient face degree. -/
theorem graphForm_eq_zero_of_internal_count {r s : ℕ}
    (edges : Fin (r + s) → Edge n m)
    (hcount : Fintype.card {q // IsInternal S (edges q)} = r)
    (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hanchor : i ∈ S → a = i)
    (x : ProductCoordinates i a b S m) (hx : (toAngular x).toFree.OpenConditions)
    (hne : ∀ q, (edges q).2 ≠ Sum.inl (edges q).1)
    (htotal : r + s = 2 * n + m - 3) (hr : r ≠ 2 * S.card - 3) :
    (graphForm edges (toAngular x)).compContinuousLinearMap (fderiv ℝ toAngular x) = 0 :=
  graphForm_eq_zero_of_dimension_mismatch edges hcount hba x hx hne
    (htotal.trans (totalDegree_eq ha hb hba hanchor).symm)
    (by simpa only [shapeDegree_eq ha hb hba] using hr)

end EnvelopingIsomorphism.Deformation.Kontsevich.InteriorGraphFaceCoordinates
