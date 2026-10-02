import EnvelopingIsomorphism.Deformation.Gauge.OperatorLimit
import Mathlib.Algebra.BigOperators.Fin

/-!
Actual formal Taylor maps on positive vector-valued power series.  Coefficients
are finite sums; the normalized Taylor operations themselves include any desired
factorial denominator.  The first-order estimate is the linearization used by
the gauge-reflection induction.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge

open EnvelopingIsomorphism.FormalSeries
open PowerSeriesModule
open scoped Classical

variable {k V W : Type*} [CommRing k]
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

abbrev TaylorFamily := (n : ℕ) → MultilinearMap k (fun _ : Fin (n + 1) => V) W

def taylorLinear (T : TaylorFamily (k := k) (V := V) (W := W)) : V →ₗ[k] W :=
  (MultilinearMap.ofSubsingleton k V W (0 : Fin 1)).symm (T 0)

def taylorApply (T : TaylorFamily (k := k) (V := V) (W := W))
    (b : PowerSeriesModule k V) : PowerSeriesModule k W :=
  mk fun d => ∑ n ∈ Finset.range d, coeffV d (applyMultilinear (T n) (fun _ => b))

@[simp] theorem coeffV_taylorApply (T : TaylorFamily (k := k) (V := V) (W := W))
    (b : PowerSeriesModule k V) (d : ℕ) :
    coeffV d (taylorApply T b) =
      ∑ n ∈ Finset.range d, coeffV d (applyMultilinear (T n) (fun _ => b)) := rfl

@[simp] theorem taylorApply_constantCoeff (T : TaylorFamily (k := k) (V := V) (W := W))
    (b : PowerSeriesModule k V) : coeffV 0 (taylorApply T b) = 0 := by simp

/-- Terms of arity greater than the requested t-degree cannot contribute. -/
theorem multilinear_coeff_zero_of_lt (m d : ℕ)
    (F : MultilinearMap k (fun _ : Fin (m + 1) => V) W)
    (b : PowerSeriesModule k V) (hb : coeffV 0 b = 0) (hd : d < m + 1) :
    coeffV d (applyMultilinear F (fun _ => b)) = 0 := by
  letI : DecidableEq (Fin (m + 1)) := Classical.decEq _
  rw [coeffV_applyMultilinear]
  apply Finset.sum_eq_zero
  intro a ha
  have hsum := (Finset.mem_piAntidiag.mp ha).1
  by_cases hz : ∃ i, a i = 0
  · obtain ⟨i, hi⟩ := hz
    exact F.map_coord_zero i (by simpa only [hi] using hb)
  · exfalso
    have hmin : m + 1 ≤ ∑ i : Fin (m + 1), a i := by
      calc
        m + 1 = ∑ _i : Fin (m + 1), (1 : ℕ) := by simp
        _ ≤ ∑ i : Fin (m + 1), a i := Finset.sum_le_sum fun i _ => by
          have hi : a i ≠ 0 := fun h => hz ⟨i, h⟩
          omega
    exact (Nat.not_le_of_lt hd) (hmin.trans_eq hsum)

/-- A unary convolution is coefficientwise application of its linear map. -/
theorem multilinear_one_coeff (F : MultilinearMap k (fun _ : Fin 1 => V) W)
    (b : PowerSeriesModule k V) (d : ℕ) :
    coeffV d (applyMultilinear F (fun _ => b)) = F (fun _ => coeffV d b) := by
  letI : DecidableEq (Fin 1) := Classical.decEq _
  rw [coeffV_applyMultilinear]
  apply Finset.sum_eq_single (fun _ : Fin 1 => d)
  · intro a ha hne
    exfalso
    apply hne
    have hsum := (Finset.mem_piAntidiag.mp ha).1
    have ha0 : a 0 = d := by simpa only [Fin.sum_univ_one] using hsum
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa only [hi] using ha0
  · intro hnot
    exfalso
    apply hnot
    rw [Finset.mem_piAntidiag]
    constructor
    · simp only [Fin.sum_univ_one]
    · intro i _; exact Finset.mem_univ i

/-- Higher Taylor operations cannot see the first unsettled coefficient. -/
theorem multilinear_higher_coeff_agree (m N : ℕ)
    (F : MultilinearMap k (fun _ : Fin (m + 2) => V) W)
    (b c : PowerSeriesModule k V) (hb : coeffV 0 b = 0) (hc : coeffV 0 c = 0)
    (hbc : AgreeBelow N b c) :
    coeffV N (applyMultilinear F (fun _ => b)) =
      coeffV N (applyMultilinear F (fun _ => c)) := by
  letI : DecidableEq (Fin (m + 2)) := Classical.decEq _
  rw [coeffV_applyMultilinear, coeffV_applyMultilinear]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hz : ∃ i, a i = 0
  · obtain ⟨i, hi⟩ := hz
    rw [F.map_coord_zero i (by simpa only [hi] using hb),
      F.map_coord_zero i (by simpa only [hi] using hc)]
  · apply congrArg F
    funext i
    apply hbc (a i)
    obtain ⟨j, hj⟩ := exists_ne i
    have hjmem : j ∈ (Finset.univ : Finset (Fin (m + 2))).erase i := by simp [hj]
    have hjle : a j ≤ ∑ k ∈ (Finset.univ : Finset (Fin (m + 2))).erase i, a k :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hjmem
    have hjpos : a j ≠ 0 := fun h => hz ⟨j, h⟩
    have hsum := (Finset.mem_piAntidiag.mp ha).1
    have herase : (∑ k ∈ (Finset.univ : Finset (Fin (m + 2))).erase i, a k) + a i = N := by
      calc
        _ = ∑ k : Fin (m + 2), a k := Finset.sum_erase_add Finset.univ a (Finset.mem_univ i)
        _ = N := hsum
    omega

/-- The leading difference of the full formal map is exactly its first Taylor component. -/
theorem taylorApply_leading_difference (T : TaylorFamily (k := k) (V := V) (W := W))
    (N : ℕ) (hN : 0 < N) (b c : PowerSeriesModule k V)
    (hb : coeffV 0 b = 0) (hc : coeffV 0 c = 0) (hbc : AgreeBelow N b c) :
    coeffV N (taylorApply T b) - coeffV N (taylorApply T c) =
      taylorLinear T (coeffV N b - coeffV N c) := by
  rw [coeffV_taylorApply, coeffV_taylorApply, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single 0]
  · rw [multilinear_one_coeff, multilinear_one_coeff]
    exact ((taylorLinear T).map_sub (coeffV N b) (coeffV N c)).symm
  · intro n hn hn0
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    rw [multilinear_higher_coeff_agree m N (T (m + 1)) b c hb hc hbc, sub_self]
  · intro hn0
    exact False.elim (hn0 (Finset.mem_range.mpr hN))

/-- Formal Taylor evaluation is continuous for the coefficient filtration on positive inputs. -/
theorem taylorApply_agree (T : TaylorFamily (k := k) (V := V) (W := W))
    (N : ℕ) (b c : PowerSeriesModule k V)
    (hb : coeffV 0 b = 0) (hc : coeffV 0 c = 0) (hbc : AgreeBelow N b c) :
    AgreeBelow N (taylorApply T b) (taylorApply T c) := by
  intro n hn
  by_cases hz : n = 0
  · subst n
    rw [taylorApply_constantCoeff, taylorApply_constantCoeff]
  · have hd := taylorApply_leading_difference T n (Nat.pos_of_ne_zero hz) b c hb hc
      (fun i hi => hbc i (hi.trans hn))
    rw [hbc n hn, sub_self, map_zero] at hd
    exact sub_eq_zero.mp hd

@[simp] theorem taylorApply_zero (T : TaylorFamily (k := k) (V := V) (W := W)) :
    taylorApply T (0 : PowerSeriesModule k V) = 0 := by
  apply PowerSeriesModule.ext
  intro d
  rw [coeffV_taylorApply, coeffV_zero]
  apply Finset.sum_eq_zero
  intro n _
  rw [coeffV_applyMultilinear]
  apply Finset.sum_eq_zero
  intro a _
  exact (T n).map_coord_zero (0 : Fin (n + 1)) rfl

end EnvelopingIsomorphism.Deformation.Gauge
