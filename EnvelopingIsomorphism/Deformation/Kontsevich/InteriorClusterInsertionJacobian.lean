import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorClusterInsertionCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.TriangularRadialJacobian
import EnvelopingIsomorphism.Deformation.Kontsevich.AnchorChangeJacobian

/-!
# The actual general interior-cluster insertion Jacobian

The target is expressed by the explicit original-label partition from
`InteriorClusterInsertionCoordinates`. Simultaneous source/target regrouping
separates the passive coarse and boundary variables. The genuine derivative
then has determinant `-r^(2 * |S| - 3)` in the angle-before-radius convention.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.InteriorClusterInsertionJacobian

open InteriorClusterInsertionCoordinates ClusterInsertionJacobian
open scoped ContDiff

variable {n m : ℕ} {i a b : Fin n} {S : Finset (Fin n)}

abbrev ShapeIndex (a b : Fin n) (S : Finset (Fin n)) :=
  Σ _ : ClusterShapeIndex a b S, Fin 2

abbrev shapeDimension (a b : Fin n) (S : Finset (Fin n)) := Fintype.card (ShapeIndex a b S)

def shapeCoordinates : (ClusterShapeIndex a b S → ℂ) ≃L[ℝ]
    (Fin (shapeDimension a b S) → ℝ) :=
  ((Pi.basis (fun _ : ClusterShapeIndex a b S => Complex.basisOneI)).reindex
    (Fintype.equivFin (ShapeIndex a b S))).equivFunL

abbrev Passive (i a : Fin n) (S : Finset (Fin n)) (m : ℕ) :=
  (ClusterCoarseIndex i a S → ℂ) × (Fin m → ℝ)

/-- Explicit simultaneous regrouping. Only the already specified shape basis
is used to turn complex shape entries into real coordinates. -/
def splitCoordinates : ClusterAngularCoordinates i a b S m ≃L[ℝ]
    Passive i a S m × Space (shapeDimension a b S) :=
  LinearEquiv.toContinuousLinearEquiv
  { toFun := fun x => ((x.1, x.2.2.1), (shapeCoordinates x.2.1, x.2.2.2))
    invFun := fun p => (p.1.1, shapeCoordinates.symm p.2.1, p.1.2, p.2.2)
    left_inv := by intro x; simp
    right_inv := by intro p; simp
    map_add' := by intros; simp
    map_smul' := by intros; simp }

@[simp] theorem splitCoordinates_apply (x : ClusterAngularCoordinates i a b S m) :
    splitCoordinates x = ((x.1, x.2.2.1), (shapeCoordinates x.2.1, x.2.2.2)) := rfl

@[simp] theorem splitCoordinates_symm_apply (p : Passive i a S m × Space (shapeDimension a b S)) :
    splitCoordinates.symm p = (p.1.1, shapeCoordinates.symm p.2.1, p.1.2, p.2.2) := rfl

def coarseCenter (u : Passive i a S m) : ℂ :=
  if h : a = i then Complex.I else u.1 ⟨a, Or.inl rfl, h⟩

theorem center_eq_coarseCenter (ha : a ∈ S) (x : ClusterAngularCoordinates i a b S m) :
    center x = coarseCenter (x.1, x.2.2.1) := by
  simp only [center, ClusterFreeCoordinates.base, ClusterFreeCoordinates.representative,
    if_pos ha, ClusterAngularCoordinates.toFree, coarseCenter]

def centerOffset (u : Passive i a S m) : Space (shapeDimension a b S) :=
  (shapeCoordinates (fun _ => coarseCenter u), Complex.equivRealProdCLM (coarseCenter u))

@[fun_prop] theorem contDiff_centerOffset :
    ContDiff ℝ ∞ (centerOffset : Passive i a S m → Space (shapeDimension a b S)) := by
  unfold centerOffset coarseCenter
  split_ifs <;> fun_prop

/-- The native insertion with its output expressed by the explicit label partition. -/
def groupedInsertion (hb : b ∈ S) (hba : b ≠ a) (hanchor : i ∈ S → a = i) :
    ClusterAngularCoordinates i a b S m → ClusterAngularCoordinates i a b S m :=
  outputCoordinates hb hba hanchor ∘ InteriorClusterInsertionCoordinates.insertion

theorem groupedInsertion_eq (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) (x : ClusterAngularCoordinates i a b S m) :
    groupedInsertion hb hba hanchor x =
      (x.1, fun j => center x + (x.2.2.2.2 : ℂ) * x.2.1 j, x.2.2.1,
        polarInsertion (Complex.equivRealProdCLM (center x)) x.2.2.2) :=
  outputCoordinates_insertion x ha hb hba hanchor

theorem shapeCoordinates_affine (z₀ : ℂ) (r : ℝ) (z : ClusterShapeIndex a b S → ℂ) :
    shapeCoordinates (fun j => z₀ + (r : ℂ) * z j) =
      shapeCoordinates (fun _ => z₀) + r • shapeCoordinates z := by
  have hf : (fun j => z₀ + (r : ℂ) * z j) = (fun _ => z₀) + r • z := by
    ext j
    simp [Complex.real_smul]
  rw [hf, map_add, map_smul]

/-- A proved conjugacy to the radial-shape map with a coarse-dependent center. -/
theorem split_groupedInsertion (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) (x : ClusterAngularCoordinates i a b S m) :
    splitCoordinates (groupedInsertion hb hba hanchor x) =
      TriangularRadialJacobian.insertion centerOffset (splitCoordinates x) := by
  rw [groupedInsertion_eq ha hb hba hanchor]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · change shapeCoordinates (fun j => center x + (x.2.2.2.2 : ℂ) * x.2.1 j) = _
      rw [shapeCoordinates_affine]
      simp only [splitCoordinates_apply, TriangularRadialJacobian.insertion,
        centerOffset, radialInsertion, Pi.zero_apply, zero_add, center_eq_coarseCenter ha]
      rfl
    · change polarInsertion (Complex.equivRealProdCLM (center x)) x.2.2.2 = _
      simp only [splitCoordinates_apply, TriangularRadialJacobian.insertion,
        centerOffset, radialInsertion, polarInsertion, Prod.fst_zero, Prod.snd_zero,
        zero_add, center_eq_coarseCenter ha, Prod.mk_add_mk]
      rfl


theorem differentiableAt_groupedInsertion (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) (x : ClusterAngularCoordinates i a b S m) :
    DifferentiableAt ℝ (groupedInsertion hb hba hanchor) x := by
  have hfun : groupedInsertion (m := m) hb hba hanchor =
      fun x => splitCoordinates.symm
        (TriangularRadialJacobian.insertion centerOffset (splitCoordinates x)) := by
    funext x
    exact splitCoordinates.injective (by
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using
        (split_groupedInsertion ha hb hba hanchor x))
  rw [hfun]
  exact splitCoordinates.symm.differentiableAt.comp x
    (((TriangularRadialJacobian.hasFDerivAt_insertion centerOffset (splitCoordinates x) _
      (contDiff_centerOffset.differentiable (by simp)).differentiableAt.hasFDerivAt).differentiableAt).comp x
        splitCoordinates.differentiableAt)

/-- Actual oriented Jacobian in the explicitly grouped original-label coordinates. -/
theorem det_fderiv_groupedInsertion (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) (x : ClusterAngularCoordinates i a b S m) :
    LinearMap.det (fderiv ℝ (groupedInsertion hb hba hanchor) x).toLinearMap =
      -x.2.2.2.2 ^ (2 * S.card - 3) := by
  have hfun : (fun p => splitCoordinates (groupedInsertion hb hba hanchor
      (splitCoordinates.symm p))) =
      (TriangularRadialJacobian.insertion centerOffset :
        Passive i a S m × Space (shapeDimension a b S) → _) := by
    funext p
    simpa using split_groupedInsertion ha hb hba hanchor (splitCoordinates.symm p)
  rw [← GraphForms.det_fderiv_linearConjugate splitCoordinates _ x
    (differentiableAt_groupedInsertion ha hb hba hanchor x), hfun,
    TriangularRadialJacobian.det_fderiv_insertion _ _
      (contDiff_centerOffset.differentiable (by simp)).differentiableAt]
  have hs : 2 ≤ S.card := by
    have hpair : ({a, b} : Finset (Fin n)) ⊆ S := by
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact ha
      · simpa only [Finset.mem_singleton.mp hj] using hb
    have h := Finset.card_le_card hpair
    simpa [Finset.card_pair (Ne.symm hba)] using h
  have hd : shapeDimension a b S + 1 = 2 * S.card - 3 := by
    simp only [shapeDimension, ShapeIndex, Fintype.card_sigma, Fintype.card_fin,
      Finset.sum_const, Finset.card_univ, smul_eq_mul,
      card_clusterShapeIndex a b S ha hb hba]
    omega
  simp only [splitCoordinates_apply, hd]

theorem det_fderiv_groupedInsertion_neg (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) (x : ClusterAngularCoordinates i a b S m)
    (hr : 0 < x.2.2.2.2) :
    LinearMap.det (fderiv ℝ (groupedInsertion hb hba hanchor) x).toLinearMap < 0 := by
  rw [det_fderiv_groupedInsertion ha hb hba hanchor]
  exact neg_neg_of_pos (pow_pos hr _)

theorem abs_det_fderiv_groupedInsertion (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) (x : ClusterAngularCoordinates i a b S m)
    (hr : 0 < x.2.2.2.2) :
    |LinearMap.det (fderiv ℝ (groupedInsertion hb hba hanchor) x).toLinearMap| =
      x.2.2.2.2 ^ (2 * S.card - 3) := by
  rw [det_fderiv_groupedInsertion ha hb hba hanchor, abs_neg,
    abs_of_pos (pow_pos hr _)]

end EnvelopingIsomorphism.Deformation.Kontsevich.InteriorClusterInsertionJacobian
