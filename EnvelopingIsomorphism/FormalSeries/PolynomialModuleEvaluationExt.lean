import EnvelopingIsomorphism.FormalSeries.PolynomialModuleCalculus
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Evaluation extensionality for true module-valued polynomials over an
infinite field, and for formal series with polynomial module coefficients.
No finite-dimensionality or uniform polynomial-degree bound is required. -/

noncomputable section

namespace PolynomialModule

variable {k V : Type*} [Field k] [Infinite k] [AddCommGroup V] [Module k V]

omit [Infinite k] in
theorem eval_equivPolynomial_self (p : PolynomialModule k k) (s : k) :
    (equivPolynomial p).eval s = eval s p := by
  induction p using induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single n a => simp [Polynomial.eval_monomial, mul_comm]

private theorem scalar_ext_of_eval_eq {p q : PolynomialModule k k}
    (h : ∀ s : k, eval s p = eval s q) : p = q := by
  apply (equivPolynomial : PolynomialModule k k ≃ₗ[k] Polynomial k).injective
  apply Polynomial.funext
  intro s
  rw [eval_equivPolynomial_self, eval_equivPolynomial_self, h]

/-- Evaluation at every field element determines every vector coefficient.
Scalar coefficient tests come from an actually constructed vector-space basis. -/
theorem ext_of_eval_eq {p q : PolynomialModule k V}
    (h : ∀ s : k, eval s p = eval s q) : p = q := by
  apply PolynomialModule.ext
  ext n
  apply (Module.Basis.ofVectorSpace k V).repr.injective
  ext b
  let f : V →ₗ[k] k := (Module.Basis.ofVectorSpace k V).coord b
  have hm : map k f p = map k f q := scalar_ext_of_eval_eq (fun s => by
    exact (eval_map k f p s).trans ((congrArg f (h s)).trans (eval_map k f q s).symm))
  exact congrArg (fun z : PolynomialModule k k => z.coeff n) hm

theorem eval_family_injective : Function.Injective (fun p : PolynomialModule k V => fun s : k => eval s p) :=
  fun _ _ h => ext_of_eval_eq (congrFun h)

theorem ext_iff_eval_eq {p q : PolynomialModule k V} : p = q ↔ ∀ s : k, eval s p = eval s q :=
  ⟨fun h _ => h ▸ rfl, ext_of_eval_eq⟩

end PolynomialModule

namespace EnvelopingIsomorphism.FormalSeries.PolynomialModuleCalculus

variable {k V : Type*} [Field k] [Infinite k] [AddCommGroup V] [Module k V]

/-- Each outer formal coefficient has its own finite polynomial support.
There is no common bound on the path degree as the outer order varies. -/
theorem series_ext_of_eval_eq {p q : PowerSeriesModule k (PolynomialModule k V)}
    (h : ∀ s : k, seriesEval s p = seriesEval s q) : p = q := by
  apply PowerSeriesModule.ext
  intro n
  apply PolynomialModule.ext_of_eval_eq
  intro s
  exact congrArg (PowerSeriesModule.coeffV n) (h s)

theorem seriesEval_family_injective :
    Function.Injective (fun p : PowerSeriesModule k (PolynomialModule k V) => fun s : k => seriesEval s p) :=
  fun _ _ h => series_ext_of_eval_eq (congrFun h)

theorem series_ext_iff_eval_eq {p q : PowerSeriesModule k (PolynomialModule k V)} :
    p = q ↔ ∀ s : k, seriesEval s p = seriesEval s q :=
  ⟨fun h _ => h ▸ rfl, series_ext_of_eval_eq⟩

end EnvelopingIsomorphism.FormalSeries.PolynomialModuleCalculus
