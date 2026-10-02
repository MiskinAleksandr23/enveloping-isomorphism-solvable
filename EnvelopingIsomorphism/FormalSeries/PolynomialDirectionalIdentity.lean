import EnvelopingIsomorphism.FormalSeries.PolynomialModuleEvaluationExt

/-! Differentiate finite multilinear polynomial identities algebraically.
The variation is an actual degree-one module polynomial; no completed-series
parameter or uniform degree hypothesis is introduced. -/

noncomputable section

namespace EnvelopingIsomorphism.FormalSeries.PolynomialDirectionalIdentity

open PolynomialModuleCalculus
open scoped BigOperators Classical

variable {k V W : Type*} [CommRing k] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

def line (b d : V) : PolynomialModule k V := PolynomialModule.single k 0 b + PolynomialModule.single k 1 d

@[simp] theorem eval_line (b d : V) (s : k) : PolynomialModule.eval s (line b d) = b + s • d := by
  simp [line]

@[simp] theorem eval_zero_line (b d : V) : PolynomialModule.eval (0 : k) (line b d) = b := by simp

@[simp] theorem eval_zero_derivative_line (b d : V) :
    PolynomialModule.eval (0 : k) (derivative (line b d)) = d := by simp [line]

def directional {r : ℕ} (F : MultilinearMap k (fun _ : Fin r => V) W) (b d : V) : W :=
  ∑ i : Fin r, F (Function.update (fun _ => b) i d)

/-- The genuine finite ordered slot sum is the derivative at zero of the
actual multilinear operation on a degree-one polynomial variation. -/
theorem eval_zero_derivative_diagonal {r : ℕ} (F : MultilinearMap k (fun _ : Fin r => V) W) (b d : V) :
    PolynomialModule.eval (0 : k) (derivative (extendMultilinear F (fun _ => line b d))) = directional F b d := by
  rw [derivative_extendMultilinear, map_sum]
  unfold directional
  apply Finset.sum_congr rfl
  intro i hi
  rw [eval_extendMultilinear]
  congr 1
  funext j
  by_cases hj : j = i
  · subst j
    simp [line]
  · simp [hj]

end EnvelopingIsomorphism.FormalSeries.PolynomialDirectionalIdentity

namespace EnvelopingIsomorphism.FormalSeries.PolynomialDirectionalIdentity

variable {k V W : Type*} [Field k] [Infinite k] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
open PolynomialModuleCalculus
open scoped BigOperators Classical

/-- A finite diagonal translation identity implies its full ordered directional
identity. Only finite polynomials are differentiated, before any completion. -/
theorem directional_of_finite_translation {ι : Type*} (S : Finset ι) (r : ι → ℕ) {m : ℕ}
    (F : MultilinearMap k (fun _ : Fin m => V) W)
    (G : (i : ι) → MultilinearMap k (fun _ : Fin (r i) => V) W) (a b d : V)
    (h : ∀ z : V, F (fun _ => a + z) - F (fun _ => a) = ∑ i ∈ S, G i (fun _ => z)) :
    directional F (a + b) d = ∑ i ∈ S, directional (G i) b d := by
  have hp : extendMultilinear F (fun _ => line (a + b) d) - PolynomialModule.single k 0 (F (fun _ => a)) =
      ∑ i ∈ S, extendMultilinear (G i) (fun _ => line b d) := by
    apply PolynomialModule.ext_of_eval_eq
    intro s
    simp only [map_sub, map_sum, eval_extendMultilinear, eval_line,
      PolynomialModule.eval_single, pow_zero, one_smul]
    simpa only [add_assoc] using h (b + s • d)
  have hd := congrArg (fun p : PolynomialModule k W => PolynomialModule.eval (0 : k) (derivative p)) hp
  simpa only [map_sub, map_sum, derivative_single_zero, map_zero, sub_zero,
    eval_zero_derivative_diagonal] using hd

end EnvelopingIsomorphism.FormalSeries.PolynomialDirectionalIdentity
