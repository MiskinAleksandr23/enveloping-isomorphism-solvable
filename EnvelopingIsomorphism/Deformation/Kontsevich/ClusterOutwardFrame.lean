import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorClusterInsertionOrientation
import EnvelopingIsomorphism.Deformation.Kontsevich.RealClusterInsertionOrientation
import Mathlib.GroupTheory.Perm.Fin

/-! The outward-normal-first sign for a coordinate basis whose radius is last.
The normal is the actual negative last coordinate vector. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ClusterOutwardFrame

variable {E : Type*} [AddCommGroup E] {d : ℕ}

def frame (v : Fin (d + 1) → E) : Fin (d + 1) → E :=
  Fin.cons (-v (Fin.last d)) (fun j => v j.castSucc)

@[simp] theorem frame_zero (v : Fin (d + 1) → E) : frame v 0 = -v (Fin.last d) := rfl

@[simp] theorem frame_succ (v : Fin (d + 1) → E) (j : Fin d) : frame v j.succ = v j.castSucc := rfl

variable [Module ℝ E]

/-- Moving the last vector to the first place and negating it contributes
exactly `(-1)^(d+1)` to every actual alternating form. -/
theorem alternatingMap_frame (f : E [⋀^Fin (d + 1)]→ₗ[ℝ] ℝ) (v : Fin (d + 1) → E) :
    f (frame v) = (-1 : ℝ) ^ (d + 1) * f v := by
  let w : Fin (d + 1) → E := Fin.cons (v (Fin.last d)) (fun j => v j.castSucc)
  have hv : v = w ∘ finRotate (d + 1) := by
    dsimp only [w, Function.comp_def]
    rw [← Fin.snoc_eq_cons_rotate]
    ext j
    refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
  have hw : f w = (-1 : ℝ) ^ d * f v := by
    calc
      f w = Equiv.Perm.sign (finRotate (d + 1)) • f (w ∘ finRotate (d + 1)) :=
        f.map_congr_perm w (finRotate (d + 1))
      _ = (-1 : ℝ) ^ d * f v := by
        rw [← hv]
        simp [sign_finRotate, Units.smul_def]
  have hn : f (frame v) = (-1 : ℝ) * f w := by
    change f.toMultilinearMap (frame v) = (-1 : ℝ) * f.toMultilinearMap w
    simpa only [neg_one_smul, smul_eq_mul, frame, w] using
      f.toMultilinearMap.cons_smul (fun j => v j.castSucc) (-1) (v (Fin.last d))
  rw [hn, hw, pow_succ]
  ring

theorem basis_det_frame (b : Module.Basis (Fin (d + 1)) ℝ E) :
    b.det (frame b) = (-1 : ℝ) ^ (d + 1) := by
  rw [alternatingMap_frame, Module.Basis.det_self, mul_one]

/-- This is the actual outward normal to the coordinate half-space `radius ≥ 0`. -/
theorem radius_outward (b : Module.Basis (Fin (d + 1)) ℝ E) :
    b.repr (frame b 0) (Fin.last d) = -1 := by
  simp [frame_zero]

theorem radius_tangent (b : Module.Basis (Fin (d + 1)) ℝ E) (j : Fin d) :
    b.repr (frame b j.succ) (Fin.last d) = 0 := by
  simp [frame_succ]

end EnvelopingIsomorphism.Deformation.Kontsevich.ClusterOutwardFrame
