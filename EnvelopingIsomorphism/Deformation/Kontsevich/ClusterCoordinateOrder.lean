import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterStandardCoordinates

/-! Explicit native coordinate order, with the radial coordinate last. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ClusterCoordinateOrder

variable (C H : Type*) [Fintype C] [Fintype H] (m : ℕ)

abbrev FaceIndex := (Σ _ : C, Fin 2) ⊕ (Σ _ : H, Fin 2) ⊕ Fin m ⊕ Unit
abbrev FullIndex := (Σ _ : C, Fin 2) ⊕ (Σ _ : H, Fin 2) ⊕ Fin m ⊕ Unit ⊕ Unit
abbrev faceDimension := Fintype.card C * 2 + (Fintype.card H * 2 + (m + 1))

def complexIndexEnum (J : Type*) [Fintype J] : (Σ _ : J, Fin 2) ≃ Fin (Fintype.card J * 2) :=
  (Equiv.sigmaEquivProd J (Fin 2)).trans
    ((Equiv.prodCongr (Fintype.equivFin J) (Equiv.refl (Fin 2))).trans finProdFinEquiv)

def faceEnum : FaceIndex C H m ≃ Fin (faceDimension C H m) :=
  (Equiv.sumCongr (complexIndexEnum C)
    ((Equiv.sumCongr (complexIndexEnum H)
      ((Equiv.sumCongr (Equiv.refl (Fin m)) (Fintype.equivFin Unit)).trans finSumFinEquiv)).trans
      finSumFinEquiv)).trans finSumFinEquiv

def radiusIndex : FullIndex C H m := .inr (.inr (.inr (.inr ())))

def indexSplit : FullIndex C H m ≃ FaceIndex C H m ⊕ Unit where
  toFun
    | .inl j => .inl (.inl j)
    | .inr (.inl j) => .inl (.inr (.inl j))
    | .inr (.inr (.inl j)) => .inl (.inr (.inr (.inl j)))
    | .inr (.inr (.inr (.inl u))) => .inl (.inr (.inr (.inr u)))
    | .inr (.inr (.inr (.inr u))) => .inr u
  invFun
    | .inl (.inl j) => .inl j
    | .inl (.inr (.inl j)) => .inr (.inl j)
    | .inl (.inr (.inr (.inl j))) => .inr (.inr (.inl j))
    | .inl (.inr (.inr (.inr u))) => .inr (.inr (.inr (.inl u)))
    | .inr u => .inr (.inr (.inr (.inr u)))
  left_inv q := by rcases q with j | j | j | u | u <;> rfl
  right_inv q := by rcases q with (j | j | j | u) | u <;> rfl

def fullEnum : FullIndex C H m ≃ Fin (faceDimension C H m + 1) :=
  (indexSplit C H m).trans
    ((Equiv.sumCongr (faceEnum C H m) (Fintype.equivFin Unit)).trans finSumFinEquiv)

@[simp] theorem fullEnum_radius :
    fullEnum C H m (radiusIndex C H m) = Fin.last (faceDimension C H m) := by
  haveI : Subsingleton (Fin (Fintype.card Unit)) := by
    rw [Fintype.card_unique]
    infer_instance
  have h : Fintype.equivFin Unit () = 0 := Subsingleton.elim _ _
  apply Fin.ext
  simp [fullEnum, indexSplit, radiusIndex, h, finSumFinEquiv_apply_right]

@[simp] theorem fullEnum_symm_last :
    (fullEnum C H m).symm (Fin.last (faceDimension C H m)) = radiusIndex C H m :=
  (fullEnum C H m).symm_apply_eq.mpr (fullEnum_radius C H m).symm

/-- Every preceding coordinate lies in the explicitly ordered native face. -/
theorem fullEnum_symm_castSucc (j : Fin (faceDimension C H m)) :
    (fullEnum C H m).symm j.castSucc =
      (indexSplit C H m).symm (.inl ((faceEnum C H m).symm j)) := by
  apply (fullEnum C H m).injective
  simp [fullEnum, finSumFinEquiv_apply_left]

end EnvelopingIsomorphism.Deformation.Kontsevich.ClusterCoordinateOrder
