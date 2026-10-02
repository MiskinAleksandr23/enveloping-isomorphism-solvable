import EnvelopingIsomorphism.Deformation.Kontsevich.SimpleFaceChartPoint
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestRealGraphDensity
import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFaceFullIntegrability

/-! A single edge order and real graph density on each marked physical face,
independent of which native chart represents that face. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestCommonRealDensity
open Configuration InteriorGraphFaceCoordinates PairedForestProductGraphDensity
open PairedForestSimpleCluster PairedForestSmoothProduct SimpleFaceNativeAtlas
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  {a b : Fin (n+1)} {T : Finset (Fin (n+1))}
  (ha : a ∈ T) (hb : b ∈ T) (hba : b ≠ a) (hg : (0 : Fin (n+1)) ∈ T → a = 0)

include hdim ha hb hba hg in
theorem degree_eq : shapeDegree a b T + coarseDegree (0 : Fin (n+1)) a T m = r := by
  rw [totalDegree_eq ha hb hba hg]
  dsimp [GraphForms.dimension] at hdim
  omega

def edges (es : Fin r → GraphForms.Edge n m) :
    Fin (shapeDegree a b T + coarseDegree (0 : Fin (n+1)) a T m) → Edge (n+1) m :=
  fun q ↦ let e := es (finCongr (degree_eq hdim ha hb hba hg) q); (e.source,e.target)

/-- Simultaneous edge/frame transport to a fixed physical label set has no
additional determinant sign. -/
theorem productDensity_eq_common (c : ChartIndex hdim a b T)
    (es : Fin r → GraphForms.Edge n m) (p : Product c.center c.orbit c.paired) :
    productDensity hdim c.center c.orbit c.paired es p =
      realFaceDensity (edges hdim ha hb hba hg es)
        (InteriorGraphFaceCoordinates.toProduct.symm (nativeEquiv hdim c p)) := by
  rcases c with ⟨x,o,ho,z,hT,ha',hb',k⟩
  subst T a b
  change productDensity hdim x o ho es p =
    realFaceDensity (framedEdges hdim x o ho es) (InteriorGraphFaceCoordinates.toProduct.symm p)
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    PairedForestRealGraphDensity.productDensity_toProduct hdim x o ho es
      (InteriorGraphFaceCoordinates.toProduct.symm p)

/-- The same linear mark transport preserves the exact DR encoding, so it
also preserves each original ambient cutoff. -/
theorem ambient_nativeEquiv (c : ChartIndex hdim a b T)
    (p : Product c.center c.orbit c.paired) :
    InteriorFaceDRCoordinates.ambient (nativeEquiv hdim c p) = InteriorFaceDRCoordinates.ambient p := by
  rcases c with ⟨x,o,ho,z,hT,ha',hb',k⟩
  subst T a b
  rfl

theorem integrable_common (es : Fin r → GraphForms.Edge n m)
    (hne : ∀ q, (es q).target ≠ Sum.inl (es q).source) :
    MeasureTheory.IntegrableOn (realFaceDensity (edges hdim ha hb hba hg es))
      (InteriorFacePartitionReassembly.FaceRegion (0 : Fin (n+1)) a b T m) :=
  InteriorFaceFullIntegrability.integrableOn_realFaceDensity _ ha hb hba
    (fun q ↦ hne (finCongr (degree_eq hdim ha hb hba hg) q))

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestCommonRealDensity
