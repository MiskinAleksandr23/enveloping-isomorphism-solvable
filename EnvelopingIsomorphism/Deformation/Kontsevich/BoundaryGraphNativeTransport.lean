import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphCanonicalFibreMatching
import EnvelopingIsomorphism.Deformation.Kontsevich.BoxStokes

/-! Native real-face measure and orientation transport through the actual
ordered product chart. All coordinate permutations are computed on the
inherited basis. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphNativeTransport
open scoped Classical BigOperators
open MeasureTheory
open BoundaryGraphFaceFactorization BoundaryGraphOrderedCoordinates BoundaryGraphOrderedIntegrals
variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

abbrev D := shapeDegree a S l u + coarseDegree i S l u
abbrev NativeReal := Fin (D (i := i) (a := a) (S := S) (l := l) (u := u)) → ℝ
abbrev OrderedReal := RealShape (a := a) (S := S) (l := l) (u := u) × RealCoarse (i := i) (S := S) (l := l) (u := u)

def nativeCoordinates : FaceCoordinates i a S m ≃L[ℝ] NativeReal (i := i) (a := a) (S := S) (l := l) (u := u) :=
  ((nativeFaceBasis.reindex (nativeIndexEnum (i := i) (a := a) (S := S) (l := l) (u := u))).equivFun).toContinuousLinearEquiv

def splitReal {r s : ℕ} : (Fin (r+s) → ℝ) ≃L[ℝ] ((Fin r → ℝ) × (Fin s → ℝ)) :=
  ((LinearEquiv.piCongrLeft ℝ (fun _ : Fin (r+s) ↦ ℝ) finSumFinEquiv).symm.trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin s) ℝ ℝ)).toContinuousLinearEquiv

def orderedRealCoordinates (hlu : l ≤ u) : FaceCoordinates i a S m ≃L[ℝ] OrderedReal (i := i) (a := a) (S := S) (l := l) (u := u) :=
  (orderedSplitFace hlu).trans
    ((GraphForms.realCoordinates (shapeN a S) (shapeM l u)).toContinuousLinearEquiv.prodCongr
      (GraphForms.realCoordinates (coarseN i S) (outsideM l u + 1)).toContinuousLinearEquiv)

def blockBoundaryPermutation (hlu : l ≤ u) : Equiv.Perm (Fin (D (i := i) (a := a) (S := S) (l := l) (u := u))) :=
  finSumFinEquiv.permCongr (Equiv.sumCongr
    (boundaryTangentPermutation (shapeN a S) (shapePermutation l u))
    (boundaryTangentPermutation (coarseN i S) (coarsePermutation hlu)))

def nativeOrderedPermutation (hlu : l ≤ u) : Equiv.Perm (Fin (D (i := i) (a := a) (S := S) (l := l) (u := u))) :=
  tangentBlockPermutation.trans (blockBoundaryPermutation hlu)

theorem nativeOrderedPermutation_sign (hlu : l ≤ u) :
    (nativeOrderedPermutation (i := i) (a := a) (S := S) hlu).sign =
      (tangentBlockPermutation (i := i) (a := a) (S := S) (l := l) (u := u)).sign * (shapePermutation l u).sign * (coarsePermutation hlu).sign := by
  simp only [nativeOrderedPermutation, blockBoundaryPermutation, Equiv.Perm.sign_trans,
    Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr, boundaryTangentPermutation_sign]
  ac_rfl

theorem splitReal_single {r s : ℕ} (j : Fin (r+s)) :
    splitReal (Pi.single j (1 : ℝ)) =
      GraphFormProduct.productVectors (fun j : Fin r ↦ Pi.single j (1 : ℝ))
        (fun j : Fin s ↦ Pi.single j (1 : ℝ)) j := by
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
  cases j with
  | inl j =>
    apply Prod.ext <;> funext k <;> simp [splitReal, LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft',
      GraphFormProduct.productVectors, Pi.single_apply]
    intro he
    have h := congrArg Fin.val he
    simp only [Fin.val_natAdd, Fin.val_castAdd] at h
    omega
  | inr j =>
    apply Prod.ext <;> funext k <;> simp [splitReal, LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft',
      GraphFormProduct.productVectors, Pi.single_apply]
    intro he
    have h := congrArg Fin.val he
    simp only [Fin.val_natAdd, Fin.val_castAdd] at h
    omega

theorem orderedSplitFace_nativeFaceBasis (hlu : l ≤ u) (j : NativeFaceIndex i a S m) :
    orderedSplitFace hlu (nativeFaceBasis j) =
      GraphFormProduct.productVectors
        (GraphForms.realBasis (shapeN a S) (shapeM l u))
        (GraphForms.realBasis (coarseN i S) (outsideM l u + 1))
        (blockBoundaryPermutation hlu (nativeIndexToBlock j)) := by
  change ((boundaryCoordinates (shapePermutation l u)).prodCongr (boundaryCoordinates (coarsePermutation hlu)))
    (splitFace (nativeFaceBasis j)) = _
  rw [splitFace_nativeFaceBasis]
  obtain ⟨k,hk⟩ := finSumFinEquiv.surjective (nativeIndexToBlock (l := l) (u := u) j)
  rw [← hk]
  cases k <;> simp [GraphFormProduct.productVectors, blockBoundaryPermutation, Equiv.permCongr,
    boundaryCoordinates_realBasis]

theorem orderedRealCoordinates_nativeFaceBasis (hlu : l ≤ u) (j : NativeFaceIndex i a S m) :
    orderedRealCoordinates hlu (nativeFaceBasis j) =
      splitReal (Pi.single (nativeOrderedPermutation hlu (nativeIndexEnum j)) (1 : ℝ)) := by
  change ((GraphForms.realCoordinates _ _).toContinuousLinearEquiv.prodCongr
    (GraphForms.realCoordinates _ _).toContinuousLinearEquiv) (orderedSplitFace hlu (nativeFaceBasis j)) = _
  rw [orderedSplitFace_nativeFaceBasis, splitReal_single]
  have hp : nativeOrderedPermutation hlu (nativeIndexEnum j) = blockBoundaryPermutation hlu (nativeIndexToBlock j) := by
    simp [nativeOrderedPermutation, tangentBlockPermutation]
  rw [hp]
  obtain ⟨k,hk⟩ := finSumFinEquiv.surjective (blockBoundaryPermutation hlu (nativeIndexToBlock j))
  rw [← hk]
  cases k <;> simp [GraphFormProduct.productVectors, GraphForms.realCoordinates] <;> funext k <;> simp [Finsupp.single_apply, Pi.single_apply, eq_comm]

theorem nativeCoordinates_basis (j : NativeFaceIndex i a S m) :
    nativeCoordinates (l := l) (u := u) (nativeFaceBasis j) = Pi.single (nativeIndexEnum j) (1 : ℝ) := by
  have he : nativeFaceBasis j =
      (nativeFaceBasis.reindex (nativeIndexEnum (l := l) (u := u))) (nativeIndexEnum j) := by simp
  rw [he]
  change (nativeFaceBasis.reindex nativeIndexEnum).equivFun _ = _
  funext k
  simp [Module.Basis.equivFun_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]

theorem nativeCoordinates_symm_single (j : Fin (D (i := i) (a := a) (S := S) (l := l) (u := u))) :
    nativeCoordinates.symm (Pi.single j (1 : ℝ)) = nativeFaceBasis (nativeIndexEnum.symm j) := by
  apply nativeCoordinates.injective
  rw [ContinuousLinearEquiv.apply_symm_apply, nativeCoordinates_basis, Equiv.apply_symm_apply]

def nativeToOrdered (hlu : l ≤ u) : NativeReal (i := i) (a := a) (S := S) (l := l) (u := u) ≃L[ℝ]
    OrderedReal (i := i) (a := a) (S := S) (l := l) (u := u) :=
  nativeCoordinates.symm.trans (orderedRealCoordinates hlu)

def permutedSplit (hlu : l ≤ u) : NativeReal (i := i) (a := a) (S := S) (l := l) (u := u) ≃L[ℝ]
    OrderedReal (i := i) (a := a) (S := S) (l := l) (u := u) :=
  ((LinearEquiv.piCongrLeft' ℝ (fun _ ↦ ℝ) (nativeOrderedPermutation hlu)).toContinuousLinearEquiv).trans splitReal

theorem nativeToOrdered_single (hlu : l ≤ u) (j : Fin (D (i := i) (a := a) (S := S) (l := l) (u := u))) :
    nativeToOrdered hlu (Pi.single j (1 : ℝ)) = permutedSplit hlu (Pi.single j (1 : ℝ)) := by
  change orderedRealCoordinates hlu (nativeCoordinates.symm (Pi.single j (1 : ℝ))) = _
  rw [nativeCoordinates_symm_single, orderedRealCoordinates_nativeFaceBasis, Equiv.apply_symm_apply]
  change splitReal (Pi.single (nativeOrderedPermutation hlu j) (1 : ℝ)) =
    splitReal (fun k ↦ (Pi.single j (1 : ℝ) : NativeReal (i := i) (a := a) (S := S) (l := l) (u := u))
      ((nativeOrderedPermutation hlu).symm k))
  apply congrArg (splitReal (r := shapeDegree a S l u) (s := coarseDegree i S l u))
  funext k
  change (Pi.single (nativeOrderedPermutation hlu j) (1 : ℝ) : NativeReal (i := i) (a := a) (S := S) (l := l) (u := u)) k =
    (Pi.single j (1 : ℝ) : NativeReal (i := i) (a := a) (S := S) (l := l) (u := u)) ((nativeOrderedPermutation hlu).symm k)
  by_cases hk : k = nativeOrderedPermutation hlu j
  · subst k
    simp only [Equiv.symm_apply_apply, Pi.single_eq_same]
  · have hj : (nativeOrderedPermutation hlu).symm k ≠ j := fun h ↦ hk (((nativeOrderedPermutation hlu).symm_apply_eq).mp h)
    simp only [Pi.single_apply, if_neg hk, if_neg hj]

private theorem cle_eq_of_single {r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F G : (Fin r → ℝ) ≃L[ℝ] E) (h : ∀ j, F (Pi.single j 1) = G (Pi.single j 1)) : F = G := by
  have hm : F.toLinearMap = G.toLinearMap := by
    apply (Pi.basisFun ℝ (Fin r)).ext
    intro j
    rw [Pi.basisFun_apply]
    exact h j
  apply ContinuousLinearEquiv.ext
  funext x
  exact congrArg (fun L : (Fin r → ℝ) →ₗ[ℝ] E ↦ L x) hm

theorem nativeToOrdered_eq (hlu : l ≤ u) :
    nativeToOrdered (i := i) (a := a) (S := S) hlu = permutedSplit hlu :=
  cle_eq_of_single _ _ (nativeToOrdered_single hlu)

theorem splitReal_measurePreserving {r s : ℕ} :
    MeasurePreserving (splitReal (r := r) (s := s)) volume (volume.prod volume) :=
  (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin r ⊕ Fin s ↦ ℝ)).comp
    ((volume_measurePreserving_piCongrLeft (fun _ : Fin (r+s) ↦ ℝ) finSumFinEquiv).symm _)

theorem nativeToOrdered_measurePreserving (hlu : l ≤ u) :
    MeasurePreserving (nativeToOrdered (i := i) (a := a) (S := S) hlu) volume (volume.prod volume) := by
  rw [nativeToOrdered_eq]
  exact splitReal_measurePreserving.comp
    ((volume_measurePreserving_piCongrLeft (fun _ ↦ ℝ) (nativeOrderedPermutation hlu).symm).symm _)

def nativeDomain : Set (NativeReal (i := i) (a := a) (S := S) (l := l) (u := u)) :=
  {x | (BoundaryClusterFreeCoordinates.faceEmbedding (nativeCoordinates.symm x)).OpenConditions l u}

def nativeRealDensity
    (edges : Fin (D (i := i) (a := a) (S := S) (l := l) (u := u)) → BoundaryGraphFaceFactorization.Edge n m)
    (x : NativeReal (i := i) (a := a) (S := S) (l := l) (u := u)) : ℝ :=
  nativeFaceDensity (l := l) (u := u) edges (nativeCoordinates.symm x)

theorem orderedRealFace_nativeToOrdered (hlu : l ≤ u)
    (x : NativeReal (i := i) (a := a) (S := S) (l := l) (u := u)) :
    orderedRealFace hlu (nativeToOrdered hlu x) = nativeCoordinates.symm x := by
  change (orderedRealCoordinates hlu).symm ((orderedRealCoordinates hlu) (nativeCoordinates.symm x)) = _
  exact ContinuousLinearEquiv.symm_apply_apply _ _

theorem nativeDomain_eq_preimage (ha : a ∈ S) (hi : i ∉ S) (hlu : l ≤ u) :
    nativeDomain (i := i) (a := a) (S := S) (l := l) (u := u) = (nativeToOrdered hlu) ⁻¹'
      (GeometricWeights.realDomain (shapeN a S) (shapeM l u) ×ˢ
        GeometricWeights.realDomain (coarseN i S) (outsideM l u + 1)) := by
  ext x
  have h := orderedRealFace_open_iff ha hi hlu (nativeToOrdered hlu x)
  rw [orderedRealFace_nativeToOrdered] at h
  exact h

/-- Exact equality of the native face Lebesgue integral and the ordered
product integral. Volume preservation is proved from the actual axis map. -/
theorem integral_native_eq_ordered (ha : a ∈ S) (hi : i ∉ S) (hlu : l ≤ u)
    (edges : Fin (D (i := i) (a := a) (S := S) (l := l) (u := u)) → BoundaryGraphFaceFactorization.Edge n m) :
    (∫ x in nativeDomain, nativeRealDensity edges x) =
      ∫ z in GeometricWeights.realDomain (shapeN a S) (shapeM l u) ×ˢ
        GeometricWeights.realDomain (coarseN i S) (outsideM l u + 1),
          orderedRealDensity edges hlu z ∂volume.prod volume := by
  have h := (nativeToOrdered_measurePreserving (i := i) (a := a) (S := S) hlu).setIntegral_preimage_emb
    (nativeToOrdered hlu).toHomeomorph.measurableEmbedding (orderedRealDensity edges hlu)
    (GeometricWeights.realDomain (shapeN a S) (shapeM l u) ×ˢ
      GeometricWeights.realDomain (coarseN i S) (outsideM l u + 1))
  rw [← nativeDomain_eq_preimage ha hi hlu] at h
  have hf : (fun x ↦ orderedRealDensity edges hlu (nativeToOrdered hlu x)) = nativeRealDensity edges := by
    funext x
    change nativeFaceDensity edges (orderedRealFace hlu (nativeToOrdered hlu x)) = _
    rw [orderedRealFace_nativeToOrdered]
    rfl
  rw [hf] at h
  exact h

end EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphNativeTransport
