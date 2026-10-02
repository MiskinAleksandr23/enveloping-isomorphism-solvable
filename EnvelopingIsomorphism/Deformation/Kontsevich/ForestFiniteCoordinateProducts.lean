import EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedShapeCoordinates

/-! Literal finite product regrouping and real/imaginary coordinate maps used
by the global free forest shape model. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestFiniteCoordinateProducts

def complexArrayHomeomorph (A : Type*) : (A → ℂ) ≃ₜ (A × Bool → ℝ) where
  toEquiv :=
    { toFun := fun q u => if u.2 then (q u.1).im else (q u.1).re
      invFun := fun q a => ⟨q (a, false), q (a, true)⟩
      left_inv := by intro q; rfl
      right_inv := by intro q; funext ⟨a, b⟩; cases b <;> rfl }
  continuous_toFun := by
    apply continuous_pi
    intro u
    cases u.2 <;> simp <;> fun_prop
  continuous_invFun := by
    apply continuous_pi
    intro a
    change Continuous (fun q : A × Bool → ℝ => Complex.equivRealProdCLM.symm (q (a, false), q (a, true)))
    exact Complex.equivRealProdCLM.symm.continuous.comp
      (show Continuous (fun q : A × Bool → ℝ => (q (a, false), q (a, true))) from
        (continuous_apply (a, false)).prodMk (continuous_apply (a, true)))

def piProductHomeomorph (A : Type*) (X Y : A → Type*) [∀ a, TopologicalSpace (X a)]
    [∀ a, TopologicalSpace (Y a)] : ((a : A) → X a × Y a) ≃ₜ ((a : A) → X a) × ((a : A) → Y a) where
  toEquiv :=
    { toFun := fun q => (fun a => (q a).1, fun a => (q a).2)
      invFun := fun q a => (q.1 a, q.2 a)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def sigmaFunctionHomeomorph (A : Type*) (B : A → Type*) (E : Type*) [TopologicalSpace E] :
    ((a : A) → B a → E) ≃ₜ ((u : Sigma B) → E) where
  toEquiv :=
    { toFun := fun q u => q u.1 u.2
      invFun := fun q a b => q ⟨a, b⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

abbrev ReflectedRealIndex (A : Type*) [Fintype A] (σ : A → A) :=
  (ReflectedShapeCoordinates.PairRep A σ × Bool) ⊕ ReflectedShapeCoordinates.Fixed A σ

def reflectedRealHomeomorph (A : Type*) [Fintype A] (σ : A → A) :
    ReflectedShapeCoordinates.Coordinates A σ ≃ₜ (ReflectedRealIndex A σ → ℝ) :=
  ((complexArrayHomeomorph (ReflectedShapeCoordinates.PairRep A σ)).prodCongr
    (Homeomorph.refl (ReflectedShapeCoordinates.Fixed A σ → ℝ))).trans
      Homeomorph.sumArrowHomeomorphProdArrow.symm

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestFiniteCoordinateProducts
