import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestFaceForms
import EnvelopingIsomorphism.Deformation.Kontsevich.StaticCollisionFaceDR

/-! Transport of literal native forest angular pair forms through an actual
smooth full-DR coordinate identity on the open strict face source. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestStaticFaceForms
open Configuration RealForestFaceForms ForestRadialFaceClassification BoxStokes Filter
open scoped Classical Topology
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (f : Coord r → E) (C : DoubledPair (n+1) m → Prop)
  (B V : DoubledPair (n+1) m → E → ℂ)
  (hambient : ∀ w : ForestRadialFaceLocalization.source hdim x o,
    StaticCollisionFaceDR.ambient C B V (f w.val) = ForestRadialFaceImmersion.forward hdim x o w.val)
  (hn : ∀ w : ForestRadialFaceLocalization.source hdim x o, ∀ p,
    StaticCollisionFaceDR.unit C B V p (f w.val) ≠ 0)
  (z : ForestRadialFaceLocalization.source hdim x o)
  (hf : ContDiffAt ℝ ⊤ f z.val)

include hambient hn hf in
theorem nativePairForm_eq_pullback (p : DoubledPair (n+1) m)
    (hB : ContDiffAt ℝ ⊤ (B p) (f z.val)) (hV : ContDiffAt ℝ ⊤ (V p) (f z.val)) :
    nativePairForm hdim x o p z.val =
      (angularPullback (StaticCollisionFaceDR.unit C B V p) (f z.val)).compContinuousLinearMap
        (fderiv ℝ f z.val) := by
  have hu : ContDiffAt ℝ ⊤ (StaticCollisionFaceDR.unit C B V p) (f z.val) := by
    unfold StaticCollisionFaceDR.unit
    split_ifs
    · exact hV
    · exact hB
  have hphase : (fun w ↦ (complexPhase (nativeUnit hdim x o p w) : ℂ)) =ᶠ[𝓝 z.val]
      (fun w ↦ (complexPhase (StaticCollisionFaceDR.unit C B V p (f w)) : ℂ)) := by
    apply eventuallyEq_of_mem ((ForestRadialFaceImmersion.isOpen_source hdim x o).mem_nhds z.property)
    intro w hw
    have h := congrArg (fun d : CompactDRCoordinates.Ambient (n+1) m ↦ d.1 p) (hambient ⟨w,hw⟩)
    change StaticCollisionFaceDR.unit C B V p (f w) / (‖StaticCollisionFaceDR.unit C B V p (f w)‖ : ℂ) =
      (complexPhase (nativeUnit hdim x o p w) : ℂ) at h
    rw [← complexPhase_coe (hn ⟨w,hw⟩ p)] at h
    exact h.symm
  unfold nativePairForm
  rw [angularPullback_eq_of_complexPhase_eventually
    (contDiff_nativeUnit hdim x o p).contDiffAt (hu.comp z.val hf)
    (nativeUnit_ne_zero hdim x o z p) (hn z p) hphase]
  exact angularPullback_comp_differentiable _ _ z.val
    (hu.differentiableAt (by simp)) (hf.differentiableAt (by simp))

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestStaticFaceForms
