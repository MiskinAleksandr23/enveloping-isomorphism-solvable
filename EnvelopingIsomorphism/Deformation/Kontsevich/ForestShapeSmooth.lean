import EnvelopingIsomorphism.Deformation.Kontsevich.ForestShapeCoordinates
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Smoothness of the explicit free-shape reconstruction formulas. Continuity
of the homeomorphisms is not used as a substitute for these calculus proofs. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestShapeSmooth

open ForestFiniteCoordinateProducts ForestShapeCoordinates ForestNodeShapeCoordinates
open ForestChildShapeDecomposition ForestMarkedFrames ComplexConjugate
open scoped Classical ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ν : ℕ∞ω}

@[fun_prop] theorem contDiff_cast (f : E → ℝ) (hf : ContDiff ℝ ν f) :
    ContDiff ℝ ν (fun e => (f e : ℂ)) := Complex.ofRealCLM.contDiff.comp hf

@[fun_prop] theorem contDiff_conj (f : E → ℂ) (hf : ContDiff ℝ ν f) :
    ContDiff ℝ ν (fun e => conj (f e)) := Complex.conjCLE.contDiff.comp hf

theorem contDiff_complex_inverse (A : Type*) [Fintype A] (r : E → (A × Bool → ℝ))
    (hr : ContDiff ℝ ν r) : ContDiff ℝ ν (fun e => (complexArrayHomeomorph A).symm (r e)) := by
  apply contDiff_pi.mpr
  intro a
  change ContDiff ℝ ν (fun e => Complex.equivRealProdCLM.symm ((r e) (a, false), (r e) (a, true)))
  exact Complex.equivRealProdCLM.symm.contDiff.comp
    ((contDiff_pi.mp hr (a, false)).prodMk (contDiff_pi.mp hr (a, true)))

theorem contDiff_reflected_inverse (A : Type*) [Fintype A] (σ : A → A)
    (hσ : Function.Involutive σ) (r : E → (ReflectedRealIndex A σ → ℝ))
    (hr : ∀ j, ContDiff ℝ ν (fun e => r e j)) (u : A) : ContDiff ℝ ν (fun e =>
      ((ReflectedShapeCoordinates.coordinatesHomeomorph A σ hσ).symm
        ((reflectedRealHomeomorph A σ).symm (r e))).val u) := by
  change ContDiff ℝ ν (fun e => ReflectedShapeCoordinates.reconstruct A σ hσ
    ((reflectedRealHomeomorph A σ).symm (r e)) u)
  unfold ReflectedShapeCoordinates.reconstruct
  split_ifs with hf hu
  · change ContDiff ℝ ν (fun e => (r e (Sum.inr ⟨u, hf⟩) : ℂ))
    exact contDiff_cast _ (hr _)
  · change ContDiff ℝ ν (fun e => Complex.equivRealProdCLM.symm
      (r e (Sum.inl (⟨u, hu⟩, false)), r e (Sum.inl (⟨u, hu⟩, true))))
    exact Complex.equivRealProdCLM.symm.contDiff.comp
      ((hr _).prodMk (hr _))
  · change ContDiff ℝ ν (fun e => conj (Complex.equivRealProdCLM.symm
      (r e (Sum.inl (_, false)), r e (Sum.inl (_, true)))))
    exact contDiff_conj _ (Complex.equivRealProdCLM.symm.contDiff.comp
      ((hr _).prodMk (hr _)))

theorem contDiff_extend (T : RootedTree) [Fintype T] (v : Parent T)
    (q : E → Child T v.val → ℂ) (hq : ContDiff ℝ ν q) :
    ContDiff ℝ ν (fun e => extend T v (q e)) := by
  apply contDiff_pi.mpr
  intro u
  unfold extend
  split_ifs
  · exact contDiff_pi.mp hq _
  · exact contDiff_const

variable (T : RootedTree) [Fintype T] (σ : T ≃o T) (hσ : Function.Involutive σ) (F : Frames T)

theorem contDiff_paired_inverse (v : PairParent T σ) (M : ComplexMarks T σ F v.val)
    (c : E → Circle) (r : E → PairedRealIndex T σ F v M → ℝ)
    (hc : ContDiff ℝ ν (fun e => (c e : ℂ))) (hr : ContDiff ℝ ν r) :
    ContDiff ℝ ν (fun e => ((pairedFactorHomeomorph T σ hσ F v M).symm
      ((pairedRealHomeomorph T σ F v M).symm (c e, r e))).val) := by
  change ContDiff ℝ ν (fun e => extend T v.val
    (complexRestore _ M.a M.b (c e, (complexArrayHomeomorph _).symm (r e))))
  apply contDiff_extend
  apply contDiff_pi.mpr
  intro u
  unfold complexRestore
  split_ifs
  · exact contDiff_const
  · exact hc
  · exact contDiff_pi.mp (contDiff_complex_inverse _ r hr) _

theorem contDiff_fixed_inverse (v : FixedParent T σ) (M : StableMarks T σ F v)
    (r : E → StableRealIndex T σ hσ F v M → ℝ)
    (hr : ∀ j, ContDiff ℝ ν (fun e => r e j)) :
    ContDiff ℝ ν (fun e => ((fixedFactorHomeomorph T σ hσ F v M).symm
      ((stableRealHomeomorph T σ hσ F v M).symm (r e))).val.val) := by
  letI : DecidableEq (Child T v.val.val) := Classical.decEq _
  cases M with
  | height a ha hf =>
    change ContDiff ℝ ν (fun e => extend T v.val
      (heightRestore _ _ (childReflection_involutive T σ hσ v) a
        ((ReflectedShapeCoordinates.coordinatesHomeomorph _ _
          (heightReflection_involutive _ _ (childReflection_involutive T σ hσ v) a)).symm
            ((reflectedRealHomeomorph _ _).symm (r e)))))
    apply contDiff_extend
    apply contDiff_pi.mpr
    intro u
    unfold heightRestore
    split_ifs
    · exact contDiff_const
    · exact contDiff_const
    · exact contDiff_reflected_inverse
        (HeightFree (Child T v.val.val) (childReflection T σ v) a)
        (heightReflection _ _ (childReflection_involutive T σ hσ v) a)
        (heightReflection_involutive _ _ (childReflection_involutive T σ hσ v) a) r hr _
  | realPair a b hne ha hb hf =>
    change ContDiff ℝ ν (fun e => extend T v.val
      (realPairRestore _ _ (childReflection_involutive T σ hσ v) a b ha hb
        ((ReflectedShapeCoordinates.coordinatesHomeomorph _ _
          (realPairReflection_involutive _ _ (childReflection_involutive T σ hσ v) a b ha hb)).symm
            ((reflectedRealHomeomorph _ _).symm (r e)))))
    apply contDiff_extend
    apply contDiff_pi.mpr
    intro u
    unfold realPairRestore
    split_ifs
    · exact contDiff_const
    · exact contDiff_const
    · exact contDiff_reflected_inverse
        (RealPairFree (Child T v.val.val) a b)
        (realPairReflection _ _ (childReflection_involutive T σ hσ v) a b ha hb)
        (realPairReflection_involutive _ _ (childReflection_involutive T σ hσ v) a b ha hb) r hr _

theorem contDiff_orbit_inverse (c : E → OrbitCoordinates T σ hσ F)
    (hc : ∀ v, ContDiff ℝ ν (fun e => ((c e).1 v).val))
    (hs : ∀ v, ContDiff ℝ ν (fun e => ((c e).2 v).val.val)) :
    ContDiff ℝ ν (fun e => ((orbitHomeomorph T σ hσ F).symm (c e)).val) := by
  apply contDiff_pi.mpr
  intro u
  change ContDiff ℝ ν (fun e => restoreArray T (fun v => restrict T v
    (ForestOrbitSections.reconstruct (Parent T) (reflectParent T σ) (reflectParent_involutive T σ hσ)
      (arrayReflection T σ hσ) (Local T σ F) (c e) v)) u)
  unfold restoreArray
  split_ifs with hu
  · exact contDiff_const
  · unfold restrict ForestOrbitSections.reconstruct
    dsimp only
    split_ifs with hf hrep
    · exact contDiff_pi.mp (hs _) _
    · exact contDiff_pi.mp (hc _) _
    · change ContDiff ℝ ν (fun e => conj (((c e).1 _).val (σ u)))
      exact contDiff_conj _ (contDiff_pi.mp (hc _) _)

theorem contDiff_shape_inverse
    (P : ∀ v : PairParent T σ, ComplexMarks T σ F v.val)
    (S : ∀ v : FixedParent T σ, StableMarks T σ F v)
    (c : E → PairParent T σ → Circle) (r : E → RealIndex T σ hσ F P S → ℝ)
    (hc : ∀ v, ContDiff ℝ ν (fun e => (c e v : ℂ))) (hr : ContDiff ℝ ν r) :
    ContDiff ℝ ν (fun e => ((shapeRealHomeomorph T σ hσ F P S).symm (c e, r e)).val) := by
  apply contDiff_orbit_inverse
  · intro v
    change ContDiff ℝ ν (fun e => ((pairedFactorHomeomorph T σ hσ F v (P v)).symm
      ((pairedRealHomeomorph T σ F v (P v)).symm
        (c e v, fun u => r e (Sum.inl ⟨v, u⟩)))).val)
    apply contDiff_paired_inverse T σ hσ F v (P v) _ _ (hc v)
    apply contDiff_pi.mpr
    intro u
    exact contDiff_pi.mp hr _
  · intro v
    change ContDiff ℝ ν (fun e => ((fixedFactorHomeomorph T σ hσ F v (S v)).symm
      ((stableRealHomeomorph T σ hσ F v (S v)).symm
        (fun u => r e (Sum.inr ⟨v, u⟩)))).val.val)
    apply contDiff_fixed_inverse T σ hσ F v (S v)
    intro u
    exact contDiff_pi.mp hr _

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestShapeSmooth
