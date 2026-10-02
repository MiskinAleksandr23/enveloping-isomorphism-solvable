import EnvelopingIsomorphism.Deformation.GraphBaseChange
import Mathlib.RingTheory.PowerSeries.Basic

/-! Coefficient convolution for actual graph operators with polynomial vertex tables. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.GraphPolynomialCoefficients

open scoped BigOperators Classical

variable {k σ : Type*} [CommRing k]

/-- Move the scalar polynomial parameter outside the coordinate polynomial ring. -/
def transpose : MvPolynomial σ (Polynomial k) →+* Polynomial (MvPolynomial σ k) :=
  MvPolynomial.eval₂Hom (Polynomial.mapRingHom MvPolynomial.C)
    (fun i ↦ Polynomial.C (MvPolynomial.X i))

theorem transpose_monomial (m : σ →₀ ℕ) (p : Polynomial k) :
    transpose (MvPolynomial.monomial m p) =
      Polynomial.map MvPolynomial.C p * Polynomial.C (MvPolynomial.monomial m 1) := by
  simp only [transpose, MvPolynomial.eval₂Hom_monomial, Polynomial.coe_mapRingHom,
    Finsupp.prod, ← map_pow, ← map_prod, MvPolynomial.prod_X_pow_eq_monomial]

/-- The parameter coefficient and the coordinate-monomial coefficient commute. -/
theorem coeff_transpose (p : MvPolynomial σ (Polynomial k)) (r : ℕ) (m : σ →₀ ℕ) :
    MvPolynomial.coeff m ((transpose p).coeff r) = (MvPolynomial.coeff m p).coeff r := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, MvPolynomial.coeff_add, hp, hq]
  | monomial a p =>
      rw [transpose_monomial, Polynomial.coeff_mul_C, Polynomial.coeff_map,
        MvPolynomial.C_mul_monomial, mul_one]
      by_cases ha : a = m <;> simp [MvPolynomial.coeff_monomial, ha]

@[simp] theorem transpose_map_C (p : MvPolynomial σ k) :
    transpose (MvPolynomial.map Polynomial.C p) = Polynomial.C p := by
  apply Polynomial.ext
  intro r
  apply MvPolynomial.ext
  intro m
  rw [coeff_transpose, MvPolynomial.coeff_map]
  by_cases hr : r = 0 <;> simp [Polynomial.coeff_C, hr]

theorem coeff_transpose_pderiv (i : σ) (p : MvPolynomial σ (Polynomial k)) (r : ℕ) :
    (transpose (MvPolynomial.pderiv i p)).coeff r =
      MvPolynomial.pderiv i ((transpose p).coeff r) := by
  apply MvPolynomial.ext
  intro m
  rw [coeff_transpose, MvPolynomial.coeff_pderiv, MvPolynomial.coeff_pderiv,
    coeff_transpose]
  rw [show (m i + 1 : Polynomial k) = Polynomial.C (m i + 1 : k) by simp,
    Polynomial.coeff_mul_C]

theorem coeff_transpose_iteratedPDeriv (is : List σ)
    (p : MvPolynomial σ (Polynomial k)) (r : ℕ) :
    (transpose (iteratedPDeriv is p)).coeff r =
      iteratedPDeriv is ((transpose p).coeff r) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [iteratedPDeriv_cons, coeff_transpose_pderiv, ih]

theorem coeff_polynomial_prod {ι R : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (p : ι → Polynomial R) (r : ℕ) :
    (∏ i, p i).coeff r =
      ∑ a ∈ Finset.piAntidiag Finset.univ r, ∏ i, (p i).coeff (a i) := by
  classical
  have h := PowerSeries.coeff_prod (fun i ↦ (p i : PowerSeries R)) r Finset.univ
  rw [Finset.finsuppAntidiag, Finset.sum_map] at h
  simp only [Polynomial.coeff_coe] at h
  change (PowerSeries.coeff r) (∏ i, (p i : PowerSeries R)) =
    ∑ a ∈ (Finset.piAntidiag Finset.univ r).attach,
      (fun a : ι → ℕ ↦ ∏ i, (p i).coeff (a i)) a.val at h
  have he : (∏ i, (p i : PowerSeries R)) = ((∏ i, p i : Polynomial R) : PowerSeries R) :=
    (map_prod Polynomial.coeToPowerSeries.ringHom p Finset.univ).symm
  rw [he, Polynomial.coeff_coe] at h
  exact h.trans (Finset.sum_attach _ (fun a : ι → ℕ ↦ ∏ i, (p i).coeff (a i)))

section Graphs

variable {n d : ℕ}

theorem coeff_transpose_linearCoefficient (c : Fin d → Polynomial k) (r : ℕ) :
    (transpose (KontsevichGraph.linearCoefficient c)).coeff r =
      KontsevichGraph.linearCoefficient (fun i ↦ (c i).coeff r) := by
  simp only [KontsevichGraph.linearCoefficient, map_sum, map_mul, transpose,
    MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', Polynomial.finsetSum_coeff,
    Polynomial.coeff_mul_C, Polynomial.coe_mapRingHom, Polynomial.coeff_map]

theorem coeff_transpose_vertexDerivative (Γ : KontsevichGraph n)
    (lab : KontsevichGraph.Edge n → Fin d) (v : KontsevichGraph.Vertex n)
    (p : MvPolynomial (Fin d) (Polynomial k)) (r : ℕ) :
    (transpose (Γ.vertexDerivative lab v p)).coeff r =
      Γ.vertexDerivative lab v ((transpose p).coeff r) :=
  coeff_transpose_iteratedPDeriv _ p r

theorem transpose_vertexDerivative_map_C (Γ : KontsevichGraph n)
    (lab : KontsevichGraph.Edge n → Fin d) (v : KontsevichGraph.Vertex n)
    (f : MvPolynomial (Fin d) k) :
    transpose (Γ.vertexDerivative lab v (MvPolynomial.map Polynomial.C f)) =
      Polynomial.C (Γ.vertexDerivative lab v f) := by
  rw [← KontsevichGraph.map_vertexDerivative Polynomial.C, transpose_map_C]

/-- The only convoluted factors are the internal vertex tables; the two exterior
polynomials are constant in the scalar parameter. -/
theorem coeff_transpose_labelledOperator (Γ : KontsevichGraph n)
    (c : KontsevichGraph.Coefficients n d (Polynomial k))
    (lab : KontsevichGraph.Edge n → Fin d) (f g : MvPolynomial (Fin d) k) (r : ℕ) :
    (transpose (Γ.labelledOperator c lab
      (MvPolynomial.map Polynomial.C f) (MvPolynomial.map Polynomial.C g))).coeff r =
      ∑ a ∈ Finset.piAntidiag Finset.univ r,
        Γ.labelledOperator (fun v i j l ↦ (c v i j l).coeff (a v)) lab f g := by
  have ht : transpose (Γ.labelledOperator c lab
      (MvPolynomial.map Polynomial.C f) (MvPolynomial.map Polynomial.C g)) =
      (∏ v : Fin n, transpose (Γ.vertexDerivative lab (Sum.inl v)
        (KontsevichGraph.linearCoefficient (c v (lab (v, 0)) (lab (v, 1)))))) *
      Polynomial.C (Γ.vertexDerivative lab (Sum.inr 0) f *
        Γ.vertexDerivative lab (Sum.inr 1) g) := by
    change transpose ((∏ v : Fin n, Γ.vertexDerivative lab (Sum.inl v)
      (KontsevichGraph.linearCoefficient (c v (lab (v, 0)) (lab (v, 1))))) *
      (Γ.vertexDerivative lab (Sum.inr 0) (MvPolynomial.map Polynomial.C f) *
        Γ.vertexDerivative lab (Sum.inr 1) (MvPolynomial.map Polynomial.C g))) = _
    rw [map_mul, map_prod, map_mul, transpose_vertexDerivative_map_C,
      transpose_vertexDerivative_map_C, ← map_mul]
  rw [ht, Polynomial.coeff_mul_C, coeff_polynomial_prod, Finset.sum_mul]
  simp_rw [coeff_transpose_vertexDerivative, coeff_transpose_linearCoefficient]
  rfl

/-- The full graph operator satisfies actual finite parameter convolution. -/
theorem coeff_transpose_operator (Γ : KontsevichGraph n)
    (c : KontsevichGraph.Coefficients n d (Polynomial k))
    (f g : MvPolynomial (Fin d) k) (r : ℕ) :
    (transpose (Γ.operator c
      (MvPolynomial.map Polynomial.C f) (MvPolynomial.map Polynomial.C g))).coeff r =
      ∑ a ∈ Finset.piAntidiag Finset.univ r,
        Γ.operator (fun v i j l ↦ (c v i j l).coeff (a v)) f g := by
  simp only [KontsevichGraph.operator_apply, map_sum, Polynomial.finsetSum_coeff,
    coeff_transpose_labelledOperator]
  exact Finset.sum_comm

/-- Coefficient formula on the actual original graph output polynomial. -/
theorem coeff_operator (Γ : KontsevichGraph n)
    (c : KontsevichGraph.Coefficients n d (Polynomial k))
    (f g : MvPolynomial (Fin d) k) (r : ℕ) (m : Fin d →₀ ℕ) :
    (MvPolynomial.coeff m (Γ.operator c
      (MvPolynomial.map Polynomial.C f) (MvPolynomial.map Polynomial.C g))).coeff r =
      ∑ a ∈ Finset.piAntidiag Finset.univ r,
        MvPolynomial.coeff m (Γ.operator (fun v i j l ↦ (c v i j l).coeff (a v)) f g) := by
  rw [← coeff_transpose, coeff_transpose_operator, MvPolynomial.coeff_sum]

theorem coeff_transpose_C_smul (a : k) (p : MvPolynomial (Fin d) (Polynomial k)) (r : ℕ) :
    (transpose (Polynomial.C a • p)).coeff r = a • (transpose p).coeff r := by
  simp only [MvPolynomial.smul_eq_C_mul, map_mul]
  simp only [transpose, MvPolynomial.eval₂Hom_C, Polynomial.coe_mapRingHom,
    Polynomial.map_C, Polynomial.coeff_C_mul]

/-- Constant graph weights commute with the same finite convolution. -/
theorem coeff_transpose_weightedOperator (s : Finset (KontsevichGraph n))
    (w : KontsevichGraph n → k) (c : KontsevichGraph.Coefficients n d (Polynomial k))
    (f g : MvPolynomial (Fin d) k) (r : ℕ) :
    (transpose (KontsevichGraph.weightedOperator s (fun Γ ↦ Polynomial.C (w Γ)) c
      (MvPolynomial.map Polynomial.C f) (MvPolynomial.map Polynomial.C g))).coeff r =
      ∑ a ∈ Finset.piAntidiag Finset.univ r,
        KontsevichGraph.weightedOperator s w
          (fun v i j l ↦ (c v i j l).coeff (a v)) f g := by
  simp only [KontsevichGraph.weightedOperator_apply, map_sum, Polynomial.finsetSum_coeff,
    coeff_transpose_C_smul, coeff_transpose_operator, Finset.smul_sum]
  exact Finset.sum_comm

theorem coeff_weightedOperator (s : Finset (KontsevichGraph n))
    (w : KontsevichGraph n → k) (c : KontsevichGraph.Coefficients n d (Polynomial k))
    (f g : MvPolynomial (Fin d) k) (r : ℕ) (m : Fin d →₀ ℕ) :
    (MvPolynomial.coeff m (KontsevichGraph.weightedOperator s (fun Γ ↦ Polynomial.C (w Γ)) c
      (MvPolynomial.map Polynomial.C f) (MvPolynomial.map Polynomial.C g))).coeff r =
      ∑ a ∈ Finset.piAntidiag Finset.univ r,
        MvPolynomial.coeff m (KontsevichGraph.weightedOperator s w
          (fun v i j l ↦ (c v i j l).coeff (a v)) f g) := by
  rw [← coeff_transpose, coeff_transpose_weightedOperator, MvPolynomial.coeff_sum]

end Graphs

end EnvelopingIsomorphism.Deformation.GraphPolynomialCoefficients
