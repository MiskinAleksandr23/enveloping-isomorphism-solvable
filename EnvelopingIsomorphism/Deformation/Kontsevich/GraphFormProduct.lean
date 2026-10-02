import EnvelopingIsomorphism.Deformation.Kontsevich.GraphForms
import Mathlib.MeasureTheory.Integral.Prod

/-! Determinant products of actual covectors, their orientation signs, and product integrals. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.GraphFormProduct

open ContinuousAlternatingMap
open MeasureTheory
open scoped BigOperators MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {r s : ℕ}

/-- The same determinant construction as the native ordered graph top form. -/
def ofCovectors (α : Fin r → E →L[ℝ] ℝ) : E [⋀^Fin r]→L[ℝ] ℝ :=
  (coordinateVolume r).compContinuousLinearMap (ContinuousLinearMap.pi α)

@[simp] theorem ofCovectors_apply (α : Fin r → E →L[ℝ] ℝ) (v : Fin r → E) :
    ofCovectors α v = Matrix.det (fun i j ↦ α j (v i)) := rfl

/-- The first ordered block is pulled from the first factor and the second from the second. -/
def productCovectors (α : Fin r → E →L[ℝ] ℝ) (β : Fin s → F →L[ℝ] ℝ) :
    Fin (r + s) → (E × F) →L[ℝ] ℝ :=
  fun i ↦ Sum.elim (fun a ↦ (α a).comp (ContinuousLinearMap.fst ℝ E F))
    (fun b ↦ (β b).comp (ContinuousLinearMap.snd ℝ E F)) (finSumFinEquiv.symm i)

/-- The product orientation lists the first-factor vectors before the second-factor vectors. -/
def productVectors (v : Fin r → E) (w : Fin s → F) : Fin (r + s) → E × F :=
  fun i ↦ Sum.elim (fun a ↦ (v a, 0)) (fun b ↦ (0, w b)) (finSumFinEquiv.symm i)

theorem productCovectors_matrix (α : Fin r → E →L[ℝ] ℝ) (β : Fin s → F →L[ℝ] ℝ)
    (v : Fin r → E) (w : Fin s → F) :
    (fun i j ↦ productCovectors α β j (productVectors v w i)) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (fun i j ↦ α j (v i)) 0 0 (fun i j ↦ β j (w i))) := by
  funext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [productCovectors, productVectors, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.fromBlocks]

/-- Block determinant factorization derived from the actual covector evaluations. -/
theorem form_product_apply (α : Fin r → E →L[ℝ] ℝ) (β : Fin s → F →L[ℝ] ℝ)
    (v : Fin r → E) (w : Fin s → F) :
    ofCovectors (productCovectors α β) (productVectors v w) =
      ofCovectors α v * ofCovectors β w := by
  rw [ofCovectors_apply, productCovectors_matrix, Matrix.det_reindex_self,
    Matrix.det_fromBlocks_zero₂₁, ofCovectors_apply, ofCovectors_apply]

/-- The covector order and tangent-vector order contribute their separate exact signs. -/
theorem ofCovectors_permuted_apply (α : Fin r → E →L[ℝ] ℝ) (v : Fin r → E)
    (σ τ : Equiv.Perm (Fin r)) :
    ofCovectors (fun j ↦ α (σ j)) (fun i ↦ v (τ i)) =
      (Equiv.Perm.sign σ : ℝ) * (Equiv.Perm.sign τ : ℝ) * ofCovectors α v := by
  rw [ofCovectors_apply]
  change (Matrix.submatrix (fun i j ↦ α (σ j) (v i)) τ id).det = _
  rw [Matrix.det_permute]
  have hs := Matrix.det_permute' σ (fun i j ↦ α j (v i))
  change Matrix.det (fun i j ↦ α (σ j) (v i)) = _ at hs
  rw [hs, ofCovectors_apply]
  ring

theorem form_product_permuted_apply (α : Fin r → E →L[ℝ] ℝ) (β : Fin s → F →L[ℝ] ℝ)
    (v : Fin r → E) (w : Fin s → F) (σ τ : Equiv.Perm (Fin (r + s))) :
    ofCovectors (fun j ↦ productCovectors α β (σ j)) (fun i ↦ productVectors v w (τ i)) =
      (Equiv.Perm.sign σ : ℝ) * (Equiv.Perm.sign τ : ℝ) *
        (ofCovectors α v * ofCovectors β w) := by
  rw [ofCovectors_permuted_apply, form_product_apply]

section GraphForms

variable {n m : ℕ}

theorem graphTopForm_eq (edges : Fin r → GraphForms.Edge n m) (x : GraphForms.Coordinates n m) :
    GraphForms.topForm edges x = ofCovectors (fun a ↦ GraphForms.edgeLinear (edges a) x) := rfl

theorem graphTopForm_pullback_eq (edges : Fin r → GraphForms.Edge n m)
    (x : GraphForms.Coordinates n m) (D : E →L[ℝ] GraphForms.Coordinates n m) :
    (GraphForms.topForm edges x).compContinuousLinearMap D =
      ofCovectors (fun a ↦ (GraphForms.edgeLinear (edges a) x).comp D) := by
  ext v
  rfl

/-- A genuine graph pullback factors when its actual covectors are the two pulled-back blocks. -/
theorem graphTopForm_pullback_product (edges : Fin (r + s) → GraphForms.Edge n m)
    (x : GraphForms.Coordinates n m) (D : (E × F) →L[ℝ] GraphForms.Coordinates n m)
    (α : Fin r → E →L[ℝ] ℝ) (β : Fin s → F →L[ℝ] ℝ)
    (h : ∀ a, (GraphForms.edgeLinear (edges a) x).comp D = productCovectors α β a)
    (v : Fin r → E) (w : Fin s → F) :
    (GraphForms.topForm edges x).compContinuousLinearMap D (productVectors v w) =
      ofCovectors α v * ofCovectors β w := by
  rw [graphTopForm_pullback_eq]
  simp_rw [h]
  exact form_product_apply α β v w

theorem graphTopForm_pullback_product_permuted (edges : Fin (r + s) → GraphForms.Edge n m)
    (x : GraphForms.Coordinates n m) (D : (E × F) →L[ℝ] GraphForms.Coordinates n m)
    (α : Fin r → E →L[ℝ] ℝ) (β : Fin s → F →L[ℝ] ℝ)
    (σ τ : Equiv.Perm (Fin (r + s)))
    (h : ∀ a, (GraphForms.edgeLinear (edges a) x).comp D = productCovectors α β (σ a))
    (v : Fin r → E) (w : Fin s → F) :
    (GraphForms.topForm edges x).compContinuousLinearMap D (fun i ↦ productVectors v w (τ i)) =
      (Equiv.Perm.sign σ : ℝ) * (Equiv.Perm.sign τ : ℝ) *
        (ofCovectors α v * ofCovectors β w) := by
  rw [graphTopForm_pullback_eq]
  simp_rw [h]
  exact form_product_permuted_apply α β v w σ τ

end GraphForms

section Integration

variable {A B : Type*}
  (α : A → Fin r → E →L[ℝ] ℝ) (β : B → Fin s → F →L[ℝ] ℝ)
  (v : Fin r → E) (w : Fin s → F)

/-- The actual determinant density of the two factor-dependent covector blocks. -/
def productDensity (z : A × B) : ℝ :=
  ofCovectors (productCovectors (α z.1) (β z.2)) (productVectors v w)

theorem productDensity_eq (z : A × B) :
    productDensity α β v w z = ofCovectors (α z.1) v * ofCovectors (β z.2) w :=
  form_product_apply (α z.1) (β z.2) v w

def permutedProductDensity (σ τ : Equiv.Perm (Fin (r + s))) (z : A × B) : ℝ :=
  ofCovectors (fun j ↦ productCovectors (α z.1) (β z.2) (σ j))
    (fun i ↦ productVectors v w (τ i))

theorem permutedProductDensity_eq (σ τ : Equiv.Perm (Fin (r + s))) (z : A × B) :
    permutedProductDensity α β v w σ τ z =
      ((Equiv.Perm.sign σ : ℝ) * (Equiv.Perm.sign τ : ℝ)) * productDensity α β v w z := by
  rw [permutedProductDensity, form_product_permuted_apply, productDensity_eq]

variable [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure A} {ν : Measure B} [SFinite μ] [SFinite ν]
  {U : Set A} {V : Set B}

/-- Actual L¹ hypotheses on the factors prove L¹ integrability of the determinant product. -/
theorem integrableOn_productDensity
    (hα : IntegrableOn (fun x ↦ ofCovectors (α x) v) U μ)
    (hβ : IntegrableOn (fun y ↦ ofCovectors (β y) w) V ν) :
    IntegrableOn (productDensity α β v w) (U ×ˢ V) (μ.prod ν) := by
  change Integrable (productDensity α β v w) ((μ.prod ν).restrict (U ×ˢ V))
  rw [← Measure.prod_restrict]
  have he : productDensity α β v w =
      (fun z : A × B ↦ ofCovectors (α z.1) v * ofCovectors (β z.2) w) :=
    funext (productDensity_eq α β v w)
  rw [he]
  exact hα.mul_prod hβ

/-- Fubini applied to this exact determinant density, with its integrability proved above. -/
theorem integral_productDensity
    (hα : IntegrableOn (fun x ↦ ofCovectors (α x) v) U μ)
    (hβ : IntegrableOn (fun y ↦ ofCovectors (β y) w) V ν) :
    (∫ z in U ×ˢ V, productDensity α β v w z ∂μ.prod ν) =
      (∫ x in U, ofCovectors (α x) v ∂μ) * ∫ y in V, ofCovectors (β y) w ∂ν := by
  rw [setIntegral_prod _ (integrableOn_productDensity α β v w hα hβ)]
  simp_rw [productDensity_eq, integral_const_mul, integral_mul_const]

theorem integrableOn_permutedProductDensity (σ τ : Equiv.Perm (Fin (r + s)))
    (hα : IntegrableOn (fun x ↦ ofCovectors (α x) v) U μ)
    (hβ : IntegrableOn (fun y ↦ ofCovectors (β y) w) V ν) :
    IntegrableOn (permutedProductDensity α β v w σ τ) (U ×ˢ V) (μ.prod ν) := by
  have he : permutedProductDensity α β v w σ τ =
      (fun z ↦ ((Equiv.Perm.sign σ : ℝ) * (Equiv.Perm.sign τ : ℝ)) * productDensity α β v w z) :=
    funext (permutedProductDensity_eq α β v w σ τ)
  rw [he]
  exact (integrableOn_productDensity α β v w hα hβ).const_mul
    ((Equiv.Perm.sign σ : ℝ) * (Equiv.Perm.sign τ : ℝ))

/-- Both independent orientation permutations persist in the actual product integral. -/
theorem integral_permutedProductDensity (σ τ : Equiv.Perm (Fin (r + s)))
    (hα : IntegrableOn (fun x ↦ ofCovectors (α x) v) U μ)
    (hβ : IntegrableOn (fun y ↦ ofCovectors (β y) w) V ν) :
    (∫ z in U ×ˢ V, permutedProductDensity α β v w σ τ z ∂μ.prod ν) =
      ((Equiv.Perm.sign σ : ℝ) * (Equiv.Perm.sign τ : ℝ)) *
        ((∫ x in U, ofCovectors (α x) v ∂μ) * ∫ y in V, ofCovectors (β y) w ∂ν) := by
  simp_rw [permutedProductDensity_eq]
  rw [integral_const_mul, integral_productDensity α β v w hα hβ]

/-- Native graph-form product integration uses individual pulled-back edge covectors,
not an assumed identity between determinant densities. -/
theorem integral_graphTopForm_pullback_product {n m : ℕ}
    (edges : Fin (r + s) → GraphForms.Edge n m)
    (x : A × B → GraphForms.Coordinates n m)
    (D : A × B → (E × F) →L[ℝ] GraphForms.Coordinates n m)
    (h : ∀ z a, (GraphForms.edgeLinear (edges a) (x z)).comp (D z) =
      productCovectors (α z.1) (β z.2) a)
    (hα : IntegrableOn (fun x ↦ ofCovectors (α x) v) U μ)
    (hβ : IntegrableOn (fun y ↦ ofCovectors (β y) w) V ν) :
    (∫ z in U ×ˢ V,
      (GraphForms.topForm edges (x z)).compContinuousLinearMap (D z) (productVectors v w) ∂μ.prod ν) =
      (∫ a in U, ofCovectors (α a) v ∂μ) * ∫ b in V, ofCovectors (β b) w ∂ν := by
  have he (z : A × B) :
      (GraphForms.topForm edges (x z)).compContinuousLinearMap (D z) (productVectors v w) =
        productDensity α β v w z := by
    rw [graphTopForm_pullback_product edges (x z) (D z) (α z.1) (β z.2) (h z),
      productDensity_eq]
  simp_rw [he]
  exact integral_productDensity α β v w hα hβ

theorem integral_graphTopForm_pullback_product_permuted {n m : ℕ}
    (edges : Fin (r + s) → GraphForms.Edge n m)
    (x : A × B → GraphForms.Coordinates n m)
    (D : A × B → (E × F) →L[ℝ] GraphForms.Coordinates n m)
    (σ τ : Equiv.Perm (Fin (r + s)))
    (h : ∀ z a, (GraphForms.edgeLinear (edges a) (x z)).comp (D z) =
      productCovectors (α z.1) (β z.2) (σ a))
    (hα : IntegrableOn (fun x ↦ ofCovectors (α x) v) U μ)
    (hβ : IntegrableOn (fun y ↦ ofCovectors (β y) w) V ν) :
    (∫ z in U ×ˢ V, (GraphForms.topForm edges (x z)).compContinuousLinearMap (D z)
      (fun i ↦ productVectors v w (τ i)) ∂μ.prod ν) =
      ((Equiv.Perm.sign σ : ℝ) * (Equiv.Perm.sign τ : ℝ)) *
        ((∫ a in U, ofCovectors (α a) v ∂μ) * ∫ b in V, ofCovectors (β b) w ∂ν) := by
  have he (z : A × B) :
      (GraphForms.topForm edges (x z)).compContinuousLinearMap (D z)
          (fun i ↦ productVectors v w (τ i)) = permutedProductDensity α β v w σ τ z := by
    rw [graphTopForm_pullback_product_permuted edges (x z) (D z) (α z.1) (β z.2) σ τ (h z),
      permutedProductDensity_eq, productDensity_eq]
  simp_rw [he]
  exact integral_permutedProductDensity α β v w σ τ hα hβ

end Integration

end EnvelopingIsomorphism.Deformation.Kontsevich.GraphFormProduct
