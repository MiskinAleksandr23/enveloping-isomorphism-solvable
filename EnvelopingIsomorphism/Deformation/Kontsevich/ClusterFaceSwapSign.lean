import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterFaceBasisSign

/-! Swapping any two groups of complex coordinate blocks preserves the actual
native face orientation, with all boundary scalars fixed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.ClusterFaceBasisSign
open ClusterCoordinateOrder
open scoped Classical
variable (C H : Type*) [Fintype C] [Fintype H] (m : ℕ)

def faceSwap : FaceIndex C H m ≃ FaceIndex H C m where
  toFun
    | .inl j => .inr (.inl j)
    | .inr (.inl j) => .inl j
    | .inr (.inr j) => .inr (.inr j)
  invFun
    | .inl j => .inr (.inl j)
    | .inr (.inl j) => .inl j
    | .inr (.inr j) => .inr (.inr j)
  left_inv j := by rcases j with j | j | j <;> rfl
  right_inv j := by rcases j with j | j | j <;> rfl

def fullSwap : FullIndex C H m ≃ FullIndex H C m :=
  (indexSplit C H m).trans
    ((Equiv.sumCongr (faceSwap C H m) (Equiv.refl Unit)).trans (indexSplit H C m).symm)

def labelSwap : Labels C H ≃ Labels H C where
  toFun
    | .inl c => .inr (.inl c)
    | .inr (.inl h) => .inl h
    | .inr (.inr u) => .inr (.inr u)
  invFun
    | .inl h => .inr (.inl h)
    | .inr (.inl c) => .inl c
    | .inr (.inr u) => .inr (.inr u)
  left_inv j := by rcases j with j | j | j <;> rfl
  right_inv j := by rcases j with j | j | j <;> rfl

theorem swapped_target : targetOfLabels C H m ((labelSwap C H).trans (labelEnum H C)) =
    (fullSwap C H m).trans (canonicalIndex H C m) := by
  ext j
  rcases j with ⟨c,k⟩ | ⟨h,k⟩ | j | u | u <;>
    simp [targetOfLabels,fullSwap,indexSplit,faceSwap,labelSwap,canonicalIndex,pairIndex]

private theorem sign_compare {A B : Type*} [Fintype A] [DecidableEq A]
    (f g h : A ≃ B) (hf : Equiv.Perm.sign (f.trans g.symm) = 1)
    (hh : Equiv.Perm.sign (h.trans g.symm) = 1) :
    Equiv.Perm.sign (f.trans h.symm) = 1 := by
  have he : f.trans h.symm = (f.trans g.symm).trans (h.trans g.symm).symm := by
    ext j
    simp
  rw [he]
  rw [Equiv.Perm.sign_trans, hf]
  have hi : Equiv.Perm.sign (h.trans g.symm).symm = 1 := by
    change Equiv.Perm.sign ((h.trans g.symm)⁻¹) = 1
    rw [map_inv, hh, inv_one]
  rw [hi]
  simp

theorem sign_full_swap (hd : faceDimension C H m + 1 = GraphForms.dimension (labelCount H C) m) :
    Equiv.Perm.sign (((fullEnum C H m).trans (finCongr hd)).trans
      ((fullSwap C H m).trans (sourceCanonical H C m)).symm) = 1 := by
  apply sign_compare _ (targetOfLabels C H m ((labelSwap C H).trans (labelEnum H C)))
  · exact sign_source_target C H m _ hd
  · rw [swapped_target]
    have he : ((fullSwap C H m).trans (sourceCanonical H C m)).trans
        ((fullSwap C H m).trans (canonicalIndex H C m)).symm =
        (fullSwap C H m).symm.permCongr
          ((sourceCanonical H C m).trans (canonicalIndex H C m).symm) := by
      ext j
      simp [Equiv.permCongr_def]
    rw [he,Equiv.Perm.sign_permCongr,sign_source_canonical]

theorem faceDimension_swap : faceDimension C H m = faceDimension H C m := by
  dsimp [faceDimension]
  omega

def faceSwapPermutation : Equiv.Perm (FaceIndex C H m) :=
  ((faceEnum C H m).trans (finCongr (faceDimension_swap C H m))).trans
    ((faceSwap C H m).trans (faceEnum H C m)).symm

private theorem fullEnum_cast :
    (fullEnum C H m).trans (finCongr (congrArg (· + 1) (faceDimension_swap C H m))) =
      (indexSplit C H m).trans
        ((Equiv.sumCongr ((faceEnum C H m).trans (finCongr (faceDimension_swap C H m)))
          (Fintype.equivFin Unit)).trans finSumFinEquiv) := by
  ext j
  rcases j with j | j | j | u | u <;>
    simp [fullEnum,indexSplit,finCongr]

/-- Swapping the coarse and shape groups crosses only even complex blocks. -/
theorem sign_face_swap_blocks : Equiv.Perm.sign (faceSwapPermutation C H m) = 1 := by
  let f := (faceEnum C H m).trans (finCongr (faceDimension_swap C H m))
  let g := (faceSwap C H m).trans (faceEnum H C m)
  let p : Equiv.Perm (FullIndex C H m) := (indexSplit C H m).symm.permCongr
    (Equiv.sumCongr (f.trans g.symm) (Equiv.refl Unit))
  have hp : p = ((fullEnum C H m).trans
      (finCongr (congrArg (· + 1) (faceDimension_swap C H m)))).trans
      ((fullSwap C H m).trans (fullEnum H C m)).symm := by
    rw [fullEnum_cast]
    ext j
    simp [p,f,g,fullEnum,fullSwap,Equiv.permCongr_def,Function.comp_def]
  have hs : Equiv.Perm.sign p = 1 := by
    rw [hp]
    have hd : faceDimension C H m + 1 = GraphForms.dimension (labelCount H C) m := by
      dsimp [faceDimension,GraphForms.dimension,labelCount]
      omega
    have he : ((fullEnum C H m).trans (finCongr (congrArg (· + 1) (faceDimension_swap C H m)))).trans
        ((fullSwap C H m).trans (fullEnum H C m)).symm =
        ((fullEnum C H m).trans (finCongr hd)).trans
          ((fullSwap C H m).trans (sourceCanonical H C m)).symm := by
      apply Equiv.ext
      intro j
      apply (fullSwap C H m).injective
      apply (fullEnum H C m).injective
      simp [sourceCanonical,finCongr]
    rw [he]
    exact sign_full_swap C H m hd
  simpa [p,Equiv.Perm.sign_sumCongr,faceSwapPermutation,f,g] using hs

end EnvelopingIsomorphism.Deformation.Kontsevich.ClusterFaceBasisSign
