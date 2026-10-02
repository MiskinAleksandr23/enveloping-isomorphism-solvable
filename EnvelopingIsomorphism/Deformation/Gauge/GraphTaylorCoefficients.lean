import EnvelopingIsomorphism.Deformation.GeneralGraphOperators
import EnvelopingIsomorphism.Deformation.LinearBivector
import EnvelopingIsomorphism.Deformation.Gauge.TaylorTwistEvaluation

/-! Actual effective homogeneous MC coefficients on polynomial bivectors.
The input weights are the effective graph weights, conventionally the labelled
geometric weights divided by the factorial of the number of internal vertices.
No further factorial or slot symmetrization is introduced here. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge.GraphTaylorCoefficients

open MvPolynomial
open scoped BigOperators
open KontsevichGraph

variable {k : Type*} [CommRing k] {d n : ℕ}

/-- Coordinate components of an actual polynomial bivector, with no HKR normalization. -/
def coordinateTensor : Multiderivation k (MvPolynomial (Fin d) k) 2 →ₗ[k]
    General.Tensor 2 d k where
  toFun F lab := F (fun i ↦ X (lab i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coordinateTensor_apply
    (F : Multiderivation k (MvPolynomial (Fin d) k) 2) (lab : Fin 2 → Fin d) :
    coordinateTensor F lab = F (fun i ↦ X (lab i)) := rfl

/-- A genuine graph operator, multilinear in its actual bivector inputs. -/
def graphCoefficient (Γ : KontsevichGraph n) :
    MultilinearMap k (fun _ : Fin n ↦ Multiderivation k (MvPolynomial (Fin d) k) 2)
      (Binary k (MvPolynomial (Fin d) k)) :=
  (cochainTwoEquiv k (MvPolynomial (Fin d) k)).toLinearMap.compMultilinearMap
    ((General.ofBinary Γ).cochainOperator.compLinearMap (fun _ ↦ coordinateTensor))

@[simp] theorem graphCoefficient_apply (Γ : KontsevichGraph n)
    (F : Fin n → Multiderivation k (MvPolynomial (Fin d) k) 2) :
    graphCoefficient Γ F = cochainTwoEquiv k (MvPolynomial (Fin d) k)
      ((General.ofBinary Γ).cochainOperator (fun v ↦ coordinateTensor (F v))) := rfl

/-- The general graph operator recovers exactly the existing linear-coefficient operator. -/
theorem graphCoefficient_eq_operator (Γ : KontsevichGraph n)
    (F : Fin n → Multiderivation k (MvPolynomial (Fin d) k) 2)
    (c : KontsevichGraph.Coefficients n d k)
    (hF : ∀ v, coordinateTensor (F v) = General.linearBivectorTensors c v) :
    graphCoefficient Γ F = Γ.operator c := by
  rw [graphCoefficient_apply, funext hF, General.cochainOperator_ofBinary]
  exact (cochainTwoEquiv k (MvPolynomial (Fin d) k)).apply_symm_apply _

@[simp] theorem coordinateTensor_linearBivectorOfCoefficients
    (c : Fin d → Fin d → Fin d → k)
    (hskew : ∀ i j r, c i j r = -c j i r) (hdiag : ∀ i r, c i i r = 0) :
    coordinateTensor (linearBivectorOfCoefficients c hskew hdiag) =
      fun lab ↦ KontsevichGraph.linearCoefficient (c (lab 0) (lab 1)) := by
  funext lab
  exact Poisson.linearBracket_X_X c (lab 0) (lab 1)

@[simp] theorem coordinateTensor_linearBivector
    {L : Type*} [LieRing L] [LieAlgebra k L] (b : Module.Basis (Fin d) k L) :
    coordinateTensor (linearBivector b) =
      fun lab ↦ KontsevichGraph.linearCoefficient (Poisson.structureCoeff b (lab 0) (lab 1)) := by
  funext lab
  exact Poisson.linearBracket_X_X (Poisson.structureCoeff b) (lab 0) (lab 1)

/-- Compatibility on independently varying genuine linear bivectors at every vertex. -/
theorem graphCoefficient_linearBivectors (Γ : KontsevichGraph n)
    (c : KontsevichGraph.Coefficients n d k)
    (hskew : ∀ v i j r, c v i j r = -c v j i r)
    (hdiag : ∀ v i r, c v i i r = 0) :
    graphCoefficient Γ (fun v ↦ linearBivectorOfCoefficients (c v) (hskew v) (hdiag v)) =
      Γ.operator c := by
  apply graphCoefficient_eq_operator
  intro v
  exact coordinateTensor_linearBivectorOfCoefficients (c v) (hskew v) (hdiag v)

/-- The actual positive-order coefficient, with the same effective weights as the graph product. -/
def weightedCoefficient (s : Finset (KontsevichGraph n)) (w : KontsevichGraph n → k) :
    MultilinearMap k (fun _ : Fin n ↦ Multiderivation k (MvPolynomial (Fin d) k) 2)
      (Binary k (MvPolynomial (Fin d) k)) :=
  ∑ Γ ∈ s, w Γ • graphCoefficient Γ

@[simp] theorem weightedCoefficient_apply (s : Finset (KontsevichGraph n))
    (w : KontsevichGraph n → k) (F : Fin n → Multiderivation k (MvPolynomial (Fin d) k) 2) :
    weightedCoefficient s w F = ∑ Γ ∈ s, w Γ • graphCoefficient Γ F := by
  simp only [weightedCoefficient, sum_apply, smul_apply]

theorem weightedCoefficient_eq_weightedOperator (s : Finset (KontsevichGraph n))
    (w : KontsevichGraph n → k) (F : Fin n → Multiderivation k (MvPolynomial (Fin d) k) 2)
    (c : KontsevichGraph.Coefficients n d k)
    (hF : ∀ v, coordinateTensor (F v) = General.linearBivectorTensors c v) :
    weightedCoefficient s w F = KontsevichGraph.weightedOperator s w c := by
  simp only [weightedCoefficient_apply, KontsevichGraph.weightedOperator,
    graphCoefficient_eq_operator _ F c hF]

/-- Effective full MC family: arity zero is ordinary multiplication, and each
positive arity is the genuine weighted graph contraction on raw bivectors. -/
def effectiveFamily
    (s : (j : ℕ) → Finset (KontsevichGraph (j + 1)))
    (w : (j : ℕ) → KontsevichGraph (j + 1) → k) :
    GraphTaylorFamily (k := k) (V := Multiderivation k (MvPolynomial (Fin d) k) 2)
      (W := Binary k (MvPolynomial (Fin d) k))
  | 0 => MultilinearMap.constOfIsEmpty k _ (LinearMap.mul k (MvPolynomial (Fin d) k))
  | j + 1 => weightedCoefficient (s j) (w j)

@[simp] theorem effectiveFamily_zero
    (s : (j : ℕ) → Finset (KontsevichGraph (j + 1)))
    (w : (j : ℕ) → KontsevichGraph (j + 1) → k)
    (F : Fin 0 → Multiderivation k (MvPolynomial (Fin d) k) 2) :
    effectiveFamily s w 0 F = LinearMap.mul k (MvPolynomial (Fin d) k) := rfl

@[simp] theorem effectiveFamily_succ
    (s : (j : ℕ) → Finset (KontsevichGraph (j + 1)))
    (w : (j : ℕ) → KontsevichGraph (j + 1) → k) (j : ℕ) :
    effectiveFamily (d := d) s w (j + 1) = weightedCoefficient (s j) (w j) := rfl

/-- The concrete effective family specializes to the same legacy weighted operator. -/
theorem effectiveFamily_linearBivectors
    (s : (j : ℕ) → Finset (KontsevichGraph (j + 1)))
    (w : (j : ℕ) → KontsevichGraph (j + 1) → k) (j : ℕ)
    (c : KontsevichGraph.Coefficients (j + 1) d k)
    (hskew : ∀ v i l r, c v i l r = -c v l i r)
    (hdiag : ∀ v i r, c v i i r = 0) :
    effectiveFamily s w (j + 1)
      (fun v ↦ linearBivectorOfCoefficients (c v) (hskew v) (hdiag v)) =
      KontsevichGraph.weightedOperator (s j) (w j) c := by
  apply weightedCoefficient_eq_weightedOperator
  intro v
  exact coordinateTensor_linearBivectorOfCoefficients (c v) (hskew v) (hdiag v)

end EnvelopingIsomorphism.Deformation.Gauge.GraphTaylorCoefficients
