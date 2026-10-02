import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import EnvelopingIsomorphism.Deformation.Kontsevich.DistinctPoleMonomial

/-!
Alternation is applied before any estimate: in a determinant of smooth rows
plus shared radial rows, no shared radial row can occur twice in a surviving
term. This is the algebraic simple-pole cancellation at a normal crossing.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.RadialPoleDeterminant

open scoped BigOperators Classical

variable {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [CommRing R]

def row (B : Matrix I I R) (ρ : J → I → R) (i : I) : Option J → I → R
  | none => B i
  | some ν => ρ ν

def coefficient (c : I → J → R) (t : J → R) (i : I) : Option J → R
  | none => 1
  | some ν => c i ν * t ν

def matrix (B : Matrix I I R) (ρ : J → I → R) (c : I → J → R) (t : J → R) :
    Matrix I I R := fun i => B i + ∑ ν, (c i ν * t ν) • ρ ν

omit [Fintype I] [DecidableEq I] [DecidableEq J] in
theorem matrix_row_eq_sum (B : Matrix I I R) (ρ : J → I → R)
    (c : I → J → R) (t : J → R) (i : I) :
    matrix B ρ c t i = ∑ a : Option J, coefficient c t i a • row B ρ i a := by
  simp [matrix, Fintype.sum_option, coefficient, row]

omit [DecidableEq J] in
theorem det_expansion (B : Matrix I I R) (ρ : J → I → R)
    (c : I → J → R) (t : J → R) :
    Matrix.det (matrix B ρ c t) = ∑ ε : I → Option J,
      (∏ i, coefficient c t i (ε i)) * Matrix.det (fun i => row B ρ i (ε i)) := by
  have he : matrix B ρ c t =
      fun i => ∑ a : Option J, coefficient c t i a • row B ρ i a :=
    funext (matrix_row_eq_sum B ρ c t)
  rw [he]
  change Matrix.detRowAlternating.toMultilinearMap
    (fun i => ∑ a : Option J, coefficient c t i a • row B ρ i a) = _
  rw [MultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro ε _
  exact Matrix.detRowAlternating.map_smul_univ
    (fun i => coefficient c t i (ε i)) (fun i => row B ρ i (ε i))

omit [Fintype J] [DecidableEq J] in
theorem det_row_eq_zero_of_repeated (B : Matrix I I R) (ρ : J → I → R)
    (ε : I → Option J) {i j : I} {ν : J} (hij : i ≠ j)
    (hi : ε i = some ν) (hj : ε j = some ν) :
    Matrix.det (fun k => row B ρ k (ε k)) = 0 := by
  apply Matrix.det_zero_of_row_eq hij
  simp only [hi, hj, row]

omit [Fintype J] [DecidableEq J] in
theorem det_row_eq_zero_of_not_distinct (B : Matrix I I R) (ρ : J → I → R)
    (ε : I → Option J)
    (hε : ¬ ∀ i j ν, ε i = some ν → ε j = some ν → i = j) :
    Matrix.det (fun i => row B ρ i (ε i)) = 0 := by
  push Not at hε
  obtain ⟨i, j, ν, hi, hj, hij⟩ := hε
  exact det_row_eq_zero_of_repeated B ρ ε hij hi hj

theorem det_expansion_distinct (B : Matrix I I R) (ρ : J → I → R)
    (c : I → J → R) (t : J → R) :
    Matrix.det (matrix B ρ c t) =
      ∑ ε ∈ Finset.univ.filter (fun ε : I → Option J =>
        ∀ i j ν, ε i = some ν → ε j = some ν → i = j),
        (∏ i, coefficient c t i (ε i)) * Matrix.det (fun i => row B ρ i (ε i)) := by
  classical
  rw [det_expansion, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ε _
  split_ifs with hε
  · rfl
  · rw [det_row_eq_zero_of_not_distinct B ρ ε hε, mul_zero]

def smoothCoefficient (B : Matrix I I R) (ρ : J → I → R) (c : I → J → R)
    (ε : I → Option J) : R :=
  (∏ i, (ε i).elim 1 (c i)) * Matrix.det (fun i => row B ρ i (ε i))

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem coefficient_eq (c : I → J → R) (t : J → R) (i : I) (a : Option J) :
    coefficient c t i a = a.elim 1 (c i) * a.elim 1 t := by
  cases a <;> simp [coefficient]

omit [Fintype J] [DecidableEq J] in
theorem summand_eq (B : Matrix I I R) (ρ : J → I → R)
    (c : I → J → R) (t : J → R) (ε : I → Option J) :
    (∏ i, coefficient c t i (ε i)) * Matrix.det (fun i => row B ρ i (ε i)) =
      smoothCoefficient B ρ c ε * ∏ i, (ε i).elim 1 t := by
  simp only [coefficient_eq, Finset.prod_mul_distrib, smoothCoefficient]
  ring

/-- Every singular parameter occurs at most once in every surviving monomial. -/
theorem det_expansion_simple_poles (B : Matrix I I R) (ρ : J → I → R)
    (c : I → J → R) (t : J → R) :
    Matrix.det (matrix B ρ c t) =
      ∑ ε ∈ Finset.univ.filter (PoleDistinct (I := I) (J := J)),
        smoothCoefficient B ρ c ε * ∏ ν ∈ usedPoles ε, t ν := by
  classical
  rw [det_expansion_distinct]
  unfold PoleDistinct
  apply Finset.sum_congr
  · ext ε
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro ε hε
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hε
  rw [summand_eq, prod_option_eq_prod_usedPoles ε hε t]

def coefficientBound (B : Matrix I I ℝ) (ρ : J → I → ℝ) (c : I → J → ℝ) : ℝ :=
  ∑ ε ∈ Finset.univ.filter (PoleDistinct (I := I) (J := J)), |smoothCoefficient B ρ c ε|

omit [DecidableEq J] in
theorem coefficientBound_nonneg (B : Matrix I I ℝ) (ρ : J → I → ℝ) (c : I → J → ℝ) :
    0 ≤ coefficientBound B ρ c :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- The determinant has only simple radial poles. Taking norms of all original
singular rows separately would lose precisely this cancellation. -/
theorem abs_det_le_simple_poles (B : Matrix I I ℝ) (ρ : J → I → ℝ)
    (c : I → J → ℝ) (t : J → ℝ) (ht : ∀ ν, 0 ≤ t ν) :
    |Matrix.det (matrix B ρ c t)| ≤ coefficientBound B ρ c * ∏ ν, max 1 (t ν) := by
  classical
  rw [det_expansion_distinct]
  simp_rw [summand_eq]
  calc
    |∑ ε ∈ Finset.univ.filter (fun ε : I → Option J =>
        ∀ i j ν, ε i = some ν → ε j = some ν → i = j),
        smoothCoefficient B ρ c ε * ∏ i, (ε i).elim 1 t| ≤
        ∑ ε ∈ Finset.univ.filter (PoleDistinct (I := I) (J := J)),
          |smoothCoefficient B ρ c ε * ∏ i, (ε i).elim 1 t| :=
      by
        simpa only [PoleDistinct] using Finset.abs_sum_le_sum_abs
          (fun ε => smoothCoefficient B ρ c ε * ∏ i, (ε i).elim 1 t)
          (Finset.univ.filter (PoleDistinct (I := I) (J := J)))
    _ ≤ ∑ ε ∈ Finset.univ.filter (PoleDistinct (I := I) (J := J)),
          |smoothCoefficient B ρ c ε| * ∏ ν, max 1 (t ν) := by
      apply Finset.sum_le_sum
      intro ε hε
      have hprod : 0 ≤ ∏ i, (ε i).elim 1 t := by
        apply Finset.prod_nonneg
        intro i _
        cases ε i <;> simp [ht]
      rw [abs_mul, abs_of_nonneg hprod]
      exact mul_le_mul_of_nonneg_left
        (prod_option_le_prod_max_one ε (Finset.mem_filter.mp hε).2 t ht) (abs_nonneg _)
    _ = coefficientBound B ρ c * ∏ ν, max 1 (t ν) := by
      rw [← Finset.sum_mul]
      rfl

end EnvelopingIsomorphism.Deformation.Kontsevich.RadialPoleDeterminant
