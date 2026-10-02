import EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedRadiusOrthant

/-! The actual closed normalized reflected parameter space for forest charts. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestParameterSpace

open Set ForestMarkedFrames ForestMarkedFrameInverse ForestInsertionDifference ComplexConjugate
open scoped Topology Classical

variable (T : RootedTree) [Fintype T] (σ : T ≃o T) (F : Frames T)

abbrev Ambient := (T → ℝ) × (T → ℂ)

def Constraints (x : Ambient T) : Prop :=
  ReflectedRadiusOrthant.Admissible T σ x.1 ∧ Normalized T F x.1 x.2 ∧
    (∀ u, x.2 (σ u) = conj (x.2 u)) ∧ x.2 ⊥ = 0

omit [Fintype T] in
theorem isClosed_radii : IsClosed {r : T → ℝ | ReflectedRadiusOrthant.Admissible T σ r} := by
  simp only [ReflectedRadiusOrthant.Admissible, setOf_and, setOf_forall]
  refine (isClosed_eq (continuous_apply ⊥) continuous_const).inter ?_
  refine (isClosed_iInter fun u => isClosed_iInter fun _ =>
    isClosed_eq (continuous_apply u) continuous_const).inter ?_
  refine (isClosed_iInter fun u =>
    isClosed_eq (continuous_apply (σ u)) (continuous_apply u)).inter ?_
  exact isClosed_iInter fun u => isClosed_le continuous_const (continuous_apply u)

theorem isClosed_normalized : IsClosed {x : Ambient T | Normalized T F x.1 x.2} := by
  simp only [Normalized, setOf_forall]
  apply isClosed_iInter
  intro v
  apply isClosed_iInter
  intro hv
  have happ (u : T) : Continuous (fun x : Ambient T => x.2 u) :=
    (continuous_apply u).comp continuous_snd
  have hpos : Continuous (fun x : Ambient T => (position T x.1 x.2 v).im) :=
    Complex.continuous_im.comp (contDiff_position T v).continuous
  cases hf : F v hv with
  | complex b c hb hc hbc =>
    simp only [setOf_and]
    exact (isClosed_eq (happ b) continuous_const).inter
      (isClosed_eq (happ c).norm continuous_const)
  | stableHeight b hb =>
    simp only [setOf_and]
    exact (isClosed_eq (happ b) continuous_const).inter (isClosed_eq hpos continuous_const)
  | stableRealPair b c hb hc hbc =>
    simp only [setOf_and]
    exact (isClosed_eq (happ b) continuous_const).inter
      ((isClosed_eq (happ c) continuous_const).inter (isClosed_eq hpos continuous_const))

theorem isClosed_constraints : IsClosed {x : Ambient T | Constraints T σ F x} := by
  simp only [Constraints, setOf_and, setOf_forall]
  refine ((isClosed_radii T σ).preimage continuous_fst).inter
    ((isClosed_normalized T F).inter ?_)
  refine (isClosed_iInter fun u => isClosed_eq
    ((continuous_apply (σ u)).comp continuous_snd)
    (Complex.continuous_conj.comp ((continuous_apply u).comp continuous_snd))).inter ?_
  exact isClosed_eq ((continuous_apply ⊥).comp continuous_snd) continuous_const

abbrev Space := {x : Ambient T // Constraints T σ F x}

instance : LocallyCompactSpace (Space T σ F) :=
  (isClosed_constraints T σ F).isLocallyClosed.locallyCompactSpace

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestParameterSpace
