import EnvelopingIsomorphism.FormalSeries.LaurentBilinear

/-! Relabelling and disjoint-group composition for genuine Laurent convolutions. -/

noncomputable section
namespace EnvelopingIsomorphism.FormalSeries.LaurentModule
open scoped BigOperators Classical

section Relabelling
variable {k ι κ V Z : Type*} [CommRing k] [Fintype ι] [Fintype κ]
  [AddCommGroup V] [Module k V] [AddCommGroup Z] [Module k Z]

/-- Permuting slots reindexes the actual finite-support integer exponent convolution. -/
theorem applyMultilinear_domDomCongr (e : ι ≃ κ)
    (F : MultilinearMap k (fun _ : ι ↦ V) Z) (x : κ → LaurentModule k V) :
    applyMultilinear (F.domDomCongr e) x = applyMultilinear F (x ∘ e) := by
  apply LaurentModule.ext
  intro d
  simp only [coeff_applyMultilinear, convolutionCoeff]
  let E : (κ → ℤ) ≃ (ι → ℤ) := Equiv.arrowCongr e.symm (Equiv.refl ℤ)
  apply finsum_eq_of_bijective E E.bijective
  intro a
  change (if ∑ i, a i = d then F (fun i ↦ coeff (x (e i)) (a (e i))) else 0) =
    (if ∑ i, a (e i) = d then F (fun i ↦ coeff (x (e i)) (a (e i))) else 0)
  rw [e.sum_comp a]

/-- Laurent evaluation remains linear in the coefficient multilinear map. -/
def applyMultilinearLinear (x : ι → LaurentModule k V) :
    MultilinearMap k (fun _ : ι ↦ V) Z →ₗ[k] LaurentModule k Z where
  toFun F := applyMultilinear F x
  map_add' F G := congrArg (fun H ↦ H x) (extendScalars_add F G)
  map_smul' c F := by
    apply LaurentModule.ext
    intro d
    simp only [coeff_applyMultilinear, coeff_smul, convolutionCoeff, RingHom.id_apply]
    rw [smul_finsum' c (term_finite F x d)]
    apply finsum_congr
    intro q
    simp only [term]
    split <;> simp

@[simp] theorem applyMultilinearLinear_apply (x : ι → LaurentModule k V)
    (F : MultilinearMap k (fun _ : ι ↦ V) Z) :
    applyMultilinearLinear x F = applyMultilinear F x := rfl

end Relabelling

section Grouped
universe u v
variable {k : Type u} [CommRing k] {V X Y Z : Type v}
  [AddCommGroup V] [Module k V] [AddCommGroup X] [Module k X]
  [AddCommGroup Y] [Module k Y] [AddCommGroup Z] [Module k Z] {a b : ℕ}

/-- A bilinear operation on two multilinear operations with disjoint input groups. -/
def groupedBilinear (B : X →ₗ[k] Y →ₗ[k] Z)
    (F : MultilinearMap k (fun _ : Fin a ↦ V) X)
    (G : MultilinearMap k (fun _ : Fin b ↦ V) Y) :
    MultilinearMap k (fun _ : Fin (a + b) ↦ V) Z :=
  let post : (Y →ₗ[k] Z) →ₗ[k] MultilinearMap k (fun _ : Fin b ↦ V) Z :=
    { toFun H := H.compMultilinearMap G
      map_add' H K := by apply MultilinearMap.ext; intro R; rfl
      map_smul' r H := by apply MultilinearMap.ext; intro R; rfl }
  (post.compMultilinearMap (B.compMultilinearMap F)).uncurrySum.domDomCongr finSumFinEquiv

@[simp] theorem groupedBilinear_apply (B : X →ₗ[k] Y →ₗ[k] Z)
    (F : MultilinearMap k (fun _ : Fin a ↦ V) X)
    (G : MultilinearMap k (fun _ : Fin b ↦ V) Y) (x : Fin (a + b) → V) :
    groupedBilinear B F G x = B (F (fun i ↦ x (Fin.castAdd b i)))
      (G (fun j ↦ x (Fin.natAdd a j))) := rfl

/-- Both stages of the nested convolution share the sum of the input lower bounds. -/
theorem boundedBelow_groupedBilinear (B : X →ₗ[k] Y →ₗ[k] Z)
    (F : MultilinearMap k (fun _ : Fin a ↦ V) X)
    (G : MultilinearMap k (fun _ : Fin b ↦ V) Y)
    (x : Fin (a + b) → LaurentModule k V) (L : Fin (a + b) → ℤ)
    (hx : ∀ i, BoundedBelow (L i) (x i)) :
    BoundedBelow (∑ i, L i) (extendBilinear B
      (applyMultilinear F (fun i ↦ x (Fin.castAdd b i)))
      (applyMultilinear G (fun j ↦ x (Fin.natAdd a j)))) := by
  rw [Fin.sum_univ_add]
  exact boundedBelow_extendBilinear B _ _
    (boundedBelow_applyMultilinear F _ (fun i ↦ hx (Fin.castAdd b i)))
    (boundedBelow_applyMultilinear G _ (fun j ↦ hx (Fin.natAdd a j)))

/-- The actual coefficient convolution of disjoint-group composition equals nested convolution.
The common lower bound and every monomial tuple are verified, including empty groups. -/
theorem extend_groupedBilinear (B : X →ₗ[k] Y →ₗ[k] Z)
    (F : MultilinearMap k (fun _ : Fin a ↦ V) X)
    (G : MultilinearMap k (fun _ : Fin b ↦ V) Y) :
    extend (groupedBilinear B F G) =
      groupedBilinear (restrictBilinear (extendBilinear B)) (extend F) (extend G) := by
  apply multilinear_ext_of_bounded _ _ 0
  · intro x L hx
    simpa only [add_zero, extend_apply] using boundedBelow_applyMultilinear (groupedBilinear B F G) x hx
  · intro x L hx
    simpa only [add_zero, groupedBilinear_apply, restrictBilinear_apply, extend_apply] using
      boundedBelow_groupedBilinear B F G x L hx
  · intro L v
    change applyMultilinear (groupedBilinear B F G) (fun i ↦ single (L i) (v i)) =
      extendBilinear B
        (applyMultilinear F (fun i ↦ single (L (Fin.castAdd b i)) (v (Fin.castAdd b i))))
        (applyMultilinear G (fun j ↦ single (L (Fin.natAdd a j)) (v (Fin.natAdd a j))))
    rw [applyMultilinear_single, applyMultilinear_single, applyMultilinear_single,
      extendBilinear_single, Fin.sum_univ_add]
    rfl

/-- Transfer holds for arbitrary independently varying Laurent inputs. -/
theorem applyMultilinear_groupedBilinear (B : X →ₗ[k] Y →ₗ[k] Z)
    (F : MultilinearMap k (fun _ : Fin a ↦ V) X)
    (G : MultilinearMap k (fun _ : Fin b ↦ V) Y)
    (x : Fin (a + b) → LaurentModule k V) :
    applyMultilinear (groupedBilinear B F G) x = extendBilinear B
      (applyMultilinear F (fun i ↦ x (Fin.castAdd b i)))
      (applyMultilinear G (fun j ↦ x (Fin.natAdd a j))) :=
  congrArg (fun H ↦ H x) (extend_groupedBilinear B F G)

theorem applyMultilinear_groupedBilinear_diagonal (B : X →ₗ[k] Y →ₗ[k] Z)
    (F : MultilinearMap k (fun _ : Fin a ↦ V) X)
    (G : MultilinearMap k (fun _ : Fin b ↦ V) Y) (ζ : LaurentModule k V) :
    applyMultilinear (groupedBilinear B F G) (fun _ ↦ ζ) = extendBilinear B
      (applyMultilinear F (fun _ ↦ ζ)) (applyMultilinear G (fun _ ↦ ζ)) :=
  applyMultilinear_groupedBilinear B F G _

end Grouped
end EnvelopingIsomorphism.FormalSeries.LaurentModule
