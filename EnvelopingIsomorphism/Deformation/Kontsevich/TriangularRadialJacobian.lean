import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterInsertionJacobian
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Passive coarse coordinates contribute determinant one, even when the
cluster center depends on them. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.TriangularRadialJacobian

open ClusterInsertionJacobian
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {d : ℕ}

def insertion (H : E → Space d) (p : E × Space d) : E × Space d :=
  (p.1, H p.1 + radialInsertion 0 0 p.2)

def derivative (H' : E →L[ℝ] Space d) (p : E × Space d) :
    (E × Space d) →L[ℝ] E × Space d :=
  (ContinuousLinearMap.fst ℝ E (Space d)).prod
    ((H'.comp (ContinuousLinearMap.fst ℝ E (Space d))) +
      (radialDerivative p.2).comp (ContinuousLinearMap.snd ℝ E (Space d)))

theorem derivative_apply (H' : E →L[ℝ] Space d) (p v : E × Space d) :
    derivative H' p v = (v.1, H' v.1 + radialDerivative p.2 v.2) := rfl

theorem hasFDerivAt_insertion (H : E → Space d) (p : E × Space d)
    (H' : E →L[ℝ] Space d) (hH : HasFDerivAt H H' p.1) :
    HasFDerivAt (insertion H) (derivative H' p) p := by
  exact (ContinuousLinearMap.fst ℝ E (Space d)).hasFDerivAt.prodMk
    ((hH.comp p (ContinuousLinearMap.fst ℝ E (Space d)).hasFDerivAt).add
      ((hasFDerivAt_radialInsertion 0 0 p.2).comp p
        (ContinuousLinearMap.snd ℝ E (Space d)).hasFDerivAt))

variable [FiniteDimensional ℝ E]

theorem det_derivative (H' : E →L[ℝ] Space d) (p : E × Space d) :
    LinearMap.det (derivative H' p).toLinearMap = -p.2.2.2 ^ (d + 1) := by
  classical
  let bE := Module.finBasis ℝ E
  let bV := coordinateBasis d
  have hm : LinearMap.toMatrix (bE.prod bV) (bE.prod bV) (derivative H' p).toLinearMap =
      Matrix.fromBlocks 1 0 (LinearMap.toMatrix bE bV H'.toLinearMap)
        (LinearMap.toMatrix bV bV (radialDerivative p.2).toLinearMap) := by
    ext i j
    cases i <;> cases j <;>
      simp [LinearMap.toMatrix_apply, derivative_apply, Module.Basis.prod_apply,
        Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr,
        Matrix.one_apply, Finsupp.single_apply, eq_comm]
  rw [← LinearMap.det_toMatrix (bE.prod bV), hm, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_one, one_mul, LinearMap.det_toMatrix, det_radialDerivative]

/-- The actual Fréchet determinant, with an arbitrary differentiable coarse-dependent center. -/
theorem det_fderiv_insertion (H : E → Space d) (p : E × Space d)
    (hH : DifferentiableAt ℝ H p.1) :
    LinearMap.det (fderiv ℝ (insertion H) p).toLinearMap = -p.2.2.2 ^ (d + 1) := by
  rw [(hasFDerivAt_insertion H p _ hH.hasFDerivAt).fderiv, det_derivative]

end EnvelopingIsomorphism.Deformation.Kontsevich.TriangularRadialJacobian
