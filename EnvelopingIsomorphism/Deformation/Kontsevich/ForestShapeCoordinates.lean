import EnvelopingIsomorphism.Deformation.Kontsevich.ForestChildShapeDecomposition
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestNodeShapeCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestOrbitSections
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestFiniteCoordinateProducts
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestMarkedFrameReflection
import EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedRadiusCoordinates

/-! Global shape coordinates obtained by actual selection of reflection orbits
of native parent-child components, followed by their explicit local factors. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestShapeCoordinates

open ForestChildShapeDecomposition ForestMarkedFrames ForestParameterProduct ComplexConjugate
open scoped Classical Topology NNReal

variable (T : RootedTree) [Fintype T] (σ : T ≃o T) (hσ : Function.Involutive σ) (F : Frames T)

def reflectArray (q : T → ℂ) (u : T) : ℂ := conj (q (σ u))

omit [Fintype T] in
include hσ in
theorem reflectArray_involutive : Function.Involutive (reflectArray T σ) := by
  intro q
  funext u
  simp [reflectArray, hσ u]

def arrayReflection : (T → ℂ) ≃ₜ (T → ℂ) where
  toEquiv := ⟨reflectArray T σ, reflectArray T σ, reflectArray_involutive T σ hσ,
    reflectArray_involutive T σ hσ⟩
  continuous_toFun := by unfold reflectArray; fun_prop
  continuous_invFun := by unfold reflectArray; fun_prop

def Supported (v : Parent T) (q : T → ℂ) : Prop := ∀ u, ¬ v.val ⋖ u → q u = 0

def restrict (v : Parent T) (q : T → ℂ) : Child T v.val → ℂ := fun u => q u.val

def extend (v : Parent T) (q : Child T v.val → ℂ) (u : T) : ℂ :=
  if hu : v.val ⋖ u then q ⟨u, hu⟩ else 0

omit [Fintype T] in
theorem extend_supported (v : Parent T) (q : Child T v.val → ℂ) : Supported T v (extend T v q) := by
  intro u hu
  simp [extend, hu]

omit [Fintype T] in
theorem restrict_extend (v : Parent T) (q : Child T v.val → ℂ) : restrict T v (extend T v q) = q := by
  funext u
  simp [restrict, extend, u.property]

omit [Fintype T] in
theorem extend_restrict (v : Parent T) (q : T → ℂ) (hq : Supported T v q) : extend T v (restrict T v q) = q := by
  funext u
  by_cases hu : v.val ⋖ u
  · simp [extend, restrict, hu]
  · simp [extend, hu, hq u hu]

omit [Fintype T] in
theorem continuous_restrict (v : Parent T) : Continuous (restrict T v) := by
  unfold restrict
  fun_prop

omit [Fintype T] in
theorem continuous_extend (v : Parent T) : Continuous (extend T v) := by
  apply continuous_pi
  intro u
  unfold extend
  split_ifs <;> fun_prop

omit [Fintype T] in
include hσ in
theorem supported_reflect (v : Parent T) (q : T → ℂ) (hq : Supported T v q) :
    Supported T (reflectParent T σ v) (reflectArray T σ q) := by
  intro u hu
  have hn : ¬ v.val ⋖ σ u := by
    intro h
    have hh := (apply_covBy_apply_iff σ).mpr h
    rw [hσ u] at hh
    exact hu hh
  simp [reflectArray, hq _ hn]

/-- Symmetric local constraint. The second normalization is redundant at
paired compatible complex frames and at fixed reflected components; retaining
it here makes orbit transport valid before selecting either kind of factor. -/
def Local (v : Parent T) : Set (T → ℂ) := {q |
  Supported T v q ∧ NodeNormalized T F v (restrict T v q) ∧
    NodeNormalized T F (reflectParent T σ v)
      (restrict T (reflectParent T σ v) (reflectArray T σ q))}

include hσ in
omit [Fintype T] in
theorem local_reflect (v : Parent T) (q : T → ℂ) (hq : q ∈ Local T σ F v) :
    reflectArray T σ q ∈ Local T σ F (reflectParent T σ v) := by
  refine ⟨supported_reflect T σ hσ v q hq.1, hq.2.2, ?_⟩
  rw [reflectParent_involutive T σ hσ v, reflectArray_involutive T σ hσ q]
  exact hq.2.1

abbrev SectionSpace := ForestOrbitSections.Sections (Parent T) (reflectParent T σ)
  (arrayReflection T σ hσ) (Local T σ F)

def extendComponents (q : Components T) (v : Parent T) : T → ℂ := extend T v (q v)

omit [Fintype T] in
include hσ in
theorem extendComponents_reflect (q : Components T) (hq : ComponentsReflection T σ q) (v : Parent T) :
    extendComponents T q (reflectParent T σ v) = reflectArray T σ (extendComponents T q v) := by
  funext u
  by_cases hu : (σ v.val) ⋖ u
  · have hchild : v.val ⋖ σ u := by
      simpa only [hσ v.val] using (apply_covBy_apply_iff σ).mpr hu
    have he := hq v ⟨σ u, hchild⟩
    have hc : reflectChild T σ v ⟨σ u, hchild⟩ = (⟨u, hu⟩ : Child T (reflectParent T σ v).val) :=
      Subtype.ext (hσ u)
    rw [hc] at he
    simpa only [extendComponents, extend, dif_pos hu, dif_pos hchild, reflectArray,
      reflectParent_val] using he
  · have hchild : ¬ v.val ⋖ σ u := by
      intro h
      exact hu (by simpa only [hσ u] using (apply_covBy_apply_iff σ).mpr h)
    simp [extendComponents, extend, hu, hchild, reflectArray, reflectParent]

def toSections (q : ComponentShapeSpace T F σ) : SectionSpace T σ hσ F := by
  refine ⟨extendComponents T q.val, ?_, extendComponents_reflect T σ hσ q.val q.property.2⟩
  intro v
  refine ⟨extend_supported T v (q.val v), ?_, ?_⟩
  · simpa only [extendComponents, restrict_extend] using q.property.1 v
  · rw [← extendComponents_reflect T σ hσ q.val q.property.2 v]
    simpa only [extendComponents, restrict_extend] using q.property.1 (reflectParent T σ v)

def fromSections (q : SectionSpace T σ hσ F) : ComponentShapeSpace T F σ := by
  refine ⟨fun v => restrict T v (q.val v), fun v => (q.property.1 v).2.1, ?_⟩
  intro v u
  have h := congrFun (q.property.2 v) (σ u.val)
  change q.val (reflectParent T σ v) (σ u.val) = conj (q.val v (σ (σ u.val))) at h
  rw [hσ u.val] at h
  exact h

omit [Fintype T] in
theorem from_toSections (q : ComponentShapeSpace T F σ) : fromSections T σ hσ F (toSections T σ hσ F q) = q := by
  apply Subtype.ext
  funext v
  exact restrict_extend T v (q.val v)

omit [Fintype T] in
theorem to_fromSections (q : SectionSpace T σ hσ F) : toSections T σ hσ F (fromSections T σ hσ F q) = q := by
  apply Subtype.ext
  funext v
  exact extend_restrict T v (q.val v) (q.property.1 v).1

def sectionHomeomorph : ComponentShapeSpace T F σ ≃ₜ SectionSpace T σ hσ F where
  toEquiv := ⟨toSections T σ hσ F, fromSections T σ hσ F,
    from_toSections T σ hσ F, to_fromSections T σ hσ F⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro v
    exact (continuous_extend T v).comp ((continuous_apply v).comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro v
    exact (continuous_restrict T v).comp ((continuous_apply v).comp continuous_subtype_val)

abbrev OrbitCoordinates := ForestOrbitSections.Coordinates (Parent T) (reflectParent T σ)
  (arrayReflection T σ hσ) (Local T σ F)

/-- Selection and reflection reconstruction, not a factorization premise. -/
def orbitHomeomorph : ShapeSpace T σ F ≃ₜ OrbitCoordinates T σ hσ F :=
  (ForestChildShapeDecomposition.shapeHomeomorph T F σ).trans
    ((sectionHomeomorph T σ hσ F).trans
      (ForestOrbitSections.homeomorph (Parent T) (reflectParent T σ)
        (reflectParent_involutive T σ hσ) (arrayReflection T σ hσ)
        (reflectArray_involutive T σ hσ) (Local T σ F) (local_reflect T σ hσ F)))

abbrev PairParent := ReflectedShapeCoordinates.PairRep (Parent T) (reflectParent T σ)
abbrev FixedParent := ReflectedShapeCoordinates.Fixed (Parent T) (reflectParent T σ)

structure ComplexMarks (v : Parent T) where
  a : Child T v.val
  b : Child T v.val
  ne : a ≠ b
  frame : F v.val v.property = .complex a.val b.val a.property b.property (fun h => ne (Subtype.ext h))
  reflected : F (reflectParent T σ v).val (reflectParent T σ v).property =
    .complex (σ a.val) (σ b.val) ((apply_covBy_apply_iff σ).mpr a.property)
      ((apply_covBy_apply_iff σ).mpr b.property) (σ.injective.ne (fun h => ne (Subtype.ext h)))

def complexMarks (hF : ForestMarkedFrameReflection.Compatible T σ F) (v : PairParent T σ) :
    ComplexMarks T σ F v.val := by
  have hn : σ v.val.val ≠ v.val.val := by
    intro h
    exact ReflectedShapeCoordinates.rep_not_fixed _ _ v.property (Subtype.ext h)
  apply Classical.choice
  obtain ⟨a, b, ha, hb, hne, hf, hrf⟩ := hF.paired v.val.val v.val.property hn
  exact ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hne (congrArg Subtype.val h), hf, hrf⟩⟩

def complexRestrict (v : Parent T) (M : ComplexMarks T σ F v) (q : Local T σ F v) :
    ForestNodeShapeCoordinates.ComplexShape (Child T v.val) M.a M.b := by
  refine ⟨restrict T v q.val, ?_⟩
  have hq := q.property.2.1
  rw [NodeNormalized, M.frame] at hq
  exact hq

def complexExtend (v : Parent T) (M : ComplexMarks T σ F v)
    (q : ForestNodeShapeCoordinates.ComplexShape (Child T v.val) M.a M.b) : Local T σ F v := by
  refine ⟨extend T v q.val, extend_supported T v q.val, ?_, ?_⟩
  · rw [NodeNormalized, M.frame]
    simpa only [restrict_extend] using q.property
  · simp only [NodeNormalized, M.reflected]
    change reflectArray T σ (extend T v q.val) (σ M.a.val) = 0 ∧
      ‖reflectArray T σ (extend T v q.val) (σ M.b.val)‖ = 1
    simp only [reflectArray]
    rw [hσ M.a.val, hσ M.b.val]
    simpa only [extend, dif_pos M.a.property, dif_pos M.b.property, map_zero, Complex.norm_conj] using
      And.intro (congrArg conj q.property.1) q.property.2

def complexLocalHomeomorph (v : Parent T) (M : ComplexMarks T σ F v) :
    Local T σ F v ≃ₜ ForestNodeShapeCoordinates.ComplexShape (Child T v.val) M.a M.b where
  toEquiv :=
    { toFun := complexRestrict T σ F v M
      invFun := complexExtend T σ hσ F v M
      left_inv := by intro q; apply Subtype.ext; exact extend_restrict T v q.val q.property.1
      right_inv := by intro q; apply Subtype.ext; exact restrict_extend T v q.val }
  continuous_toFun := ((continuous_restrict T v).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_extend T v).comp continuous_subtype_val).subtype_mk _

abbrev FixedLocal (v : FixedParent T σ) :=
  {q : Local T σ F v.val // arrayReflection T σ hσ q.val = q.val}

abbrev StableShape (v : FixedParent T σ) := {q : Child T v.val.val → ℂ |
  NodeNormalized T F v.val q ∧ ∀ u,
    q (stableChildReflection T σ v.val.val (congrArg Subtype.val v.property) u) = conj (q u)}

def stableRestrict (v : FixedParent T σ) (q : FixedLocal T σ hσ F v) : StableShape T σ F v := by
  refine ⟨restrict T v.val q.val.val, q.val.property.2.1, ?_⟩
  intro u
  have he := congrFun q.property u.val
  change conj (q.val.val (σ u.val)) = q.val.val u.val at he
  change q.val.val (σ u.val) = conj (q.val.val u.val)
  simpa only [Complex.conj_conj] using congrArg conj he

include hσ in
omit [Fintype T] in
theorem extend_stable_reflect (v : FixedParent T σ) (q : StableShape T σ F v) :
    reflectArray T σ (extend T v.val q.val) = extend T v.val q.val := by
  funext u
  have hv : σ v.val.val = v.val.val := congrArg Subtype.val v.property
  by_cases hu : v.val.val ⋖ u
  · have hru : v.val.val ⋖ σ u := by simpa only [hv] using (apply_covBy_apply_iff σ).mpr hu
    have he := q.property.2 ⟨u, hu⟩
    change q.val ⟨σ u, hru⟩ = conj (q.val ⟨u, hu⟩) at he
    simp only [reflectArray, extend, dif_pos hu, dif_pos hru, he, Complex.conj_conj]
  · have hru : ¬ v.val.val ⋖ σ u := by
      intro h
      exact hu (by simpa only [hv, hσ u] using (apply_covBy_apply_iff σ).mpr h)
    simp [reflectArray, extend, hu, hru]

def stableExtend (v : FixedParent T σ) (q : StableShape T σ F v) : FixedLocal T σ hσ F v := by
  have he := extend_stable_reflect T σ hσ F v q
  refine ⟨⟨extend T v.val q.val, extend_supported T v.val q.val, ?_, ?_⟩, he⟩
  · simpa only [restrict_extend] using q.property.1
  · rw [v.property, he, restrict_extend]
    exact q.property.1

def stableLocalHomeomorph (v : FixedParent T σ) : FixedLocal T σ hσ F v ≃ₜ StableShape T σ F v where
  toEquiv :=
    { toFun := stableRestrict T σ hσ F v
      invFun := stableExtend T σ hσ F v
      left_inv := by intro q; apply Subtype.ext; apply Subtype.ext; exact extend_restrict T v.val q.val.val q.val.property.1
      right_inv := by intro q; apply Subtype.ext; exact restrict_extend T v.val q.val }
  continuous_toFun := ((continuous_restrict T v.val).comp
    (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun := (((continuous_extend T v.val).comp continuous_subtype_val).subtype_mk _).subtype_mk _

abbrev childReflection (v : FixedParent T σ) :=
  stableChildReflection T σ v.val.val (congrArg Subtype.val v.property)

omit [Fintype T] in
include hσ in
theorem childReflection_involutive (v : FixedParent T σ) : Function.Involutive (childReflection T σ v) :=
  stableChildReflection_involutive T σ hσ _ _

inductive StableMarks (v : FixedParent T σ) where
  | height (a : Child T v.val.val) (ha : childReflection T σ v a ≠ a)
      (frame : F v.val.val v.val.property = .stableHeight a.val a.property)
  | realPair (a b : Child T v.val.val) (hne : a ≠ b)
      (ha : childReflection T σ v a = a) (hb : childReflection T σ v b = b)
      (frame : F v.val.val v.val.property =
        .stableRealPair a.val b.val a.property b.property (fun h => hne (Subtype.ext h)))

/-- Actual geometric metadata for the two real marks. Height nonfixity is
derived separately from an actual inhabited normalized shape. -/
def RealPairFixed : Prop := ∀ v hv a b ha hb hne,
  F v hv = .stableRealPair a b ha hb hne → σ a = a ∧ σ b = b

def stableMarks (hF : ForestMarkedFrameReflection.Compatible T σ F) (hreal : RealPairFixed T σ F)
    (w : ShapeSpace T σ F) (v : FixedParent T σ) : StableMarks T σ F v := by
  apply Classical.choice
  have hv : σ v.val.val = v.val.val := congrArg Subtype.val v.property
  rcases hF.stable v.val.val v.val.property hv with ⟨a, ha, hf⟩ | ⟨a, b, ha, hb, hne, hf⟩
  · have hn := w.property.1 v.val.val v.val.property
    rw [hf] at hn
    have hnon : σ a ≠ a := by
      intro he
      have hi := congrArg Complex.im (w.property.2.1 a)
      rw [he, hn] at hi
      norm_num at hi
    exact ⟨.height ⟨a, ha⟩ (fun h => hnon (congrArg Subtype.val h)) hf⟩
  · have hfix := hreal v.val.val v.val.property a b ha hb hne hf
    exact ⟨.realPair ⟨a, ha⟩ ⟨b, hb⟩ (fun h => hne (congrArg Subtype.val h))
      (Subtype.ext hfix.1) (Subtype.ext hfix.2) hf⟩

abbrev StableFactor (v : FixedParent T σ) (M : StableMarks T σ F v) : Type _ :=
  letI : DecidableEq (Child T v.val.val) := Classical.decEq _
  match M with
  | .height a _ _ => ReflectedShapeCoordinates.Coordinates
      (ForestNodeShapeCoordinates.HeightFree (Child T v.val.val) (childReflection T σ v) a)
      (ForestNodeShapeCoordinates.heightReflection _ _ (childReflection_involutive T σ hσ v) a)
  | .realPair a b _ ha hb _ => ReflectedShapeCoordinates.Coordinates
      (ForestNodeShapeCoordinates.RealPairFree (Child T v.val.val) a b)
      (ForestNodeShapeCoordinates.realPairReflection _ _ (childReflection_involutive T σ hσ v) a b ha hb)

instance stableFactorTopology (v : FixedParent T σ) (M : StableMarks T σ F v) :
    TopologicalSpace (StableFactor T σ hσ F v M) := by
  cases M <;> unfold StableFactor <;> infer_instance

def stableNodeHomeomorph (v : FixedParent T σ) (M : StableMarks T σ F v) :
    StableShape T σ F v ≃ₜ StableFactor T σ hσ F v M := by
  cases M with
  | height a ha hf =>
    have hs : StableShape T σ F v = {q : Child T v.val.val → ℂ |
        (∀ u, q (childReflection T σ v u) = conj (q u)) ∧ q a = Complex.I} := by
      ext q
      change (NodeNormalized T F v.val q ∧ _) ↔ _
      rw [NodeNormalized, hf]
      exact and_comm
    dsimp only [StableFactor, stableFactorTopology]
    exact (Homeomorph.setCongr hs).trans
      (ForestNodeShapeCoordinates.heightHomeomorph _ _ (childReflection_involutive T σ hσ v) a ha)
  | realPair a b hne ha hb hf =>
    have hs : StableShape T σ F v = {q : Child T v.val.val → ℂ |
        (∀ u, q (childReflection T σ v u) = conj (q u)) ∧ q a = 0 ∧ q b = 1} := by
      ext q
      change (NodeNormalized T F v.val q ∧ _) ↔ _
      rw [NodeNormalized, hf]
      exact and_comm
    dsimp only [StableFactor, stableFactorTopology]
    exact (Homeomorph.setCongr hs).trans
      (ForestNodeShapeCoordinates.realPairHomeomorph _ _ (childReflection_involutive T σ hσ v) a b hne ha hb)

abbrev PairedFactor (v : PairParent T σ) (M : ComplexMarks T σ F v.val) : Type _ :=
  Circle × (ForestNodeShapeCoordinates.ComplexFree (Child T v.val.val) M.a M.b → ℂ)

def pairedFactorHomeomorph (v : PairParent T σ) (M : ComplexMarks T σ F v.val) :
    Local T σ F v.val ≃ₜ PairedFactor T σ F v M :=
  (complexLocalHomeomorph T σ hσ F v.val M).trans
    (ForestNodeShapeCoordinates.complexHomeomorph _ M.a M.b M.ne)

def fixedFactorHomeomorph (v : FixedParent T σ) (M : StableMarks T σ F v) :
    FixedLocal T σ hσ F v ≃ₜ StableFactor T σ hσ F v M :=
  (stableLocalHomeomorph T σ hσ F v).trans (stableNodeHomeomorph T σ hσ F v M)

/-- A finite product of literal circle/complex factors for paired parents and
complex-pair/real-fixed factors for stable parents. All reflection equations
have been discharged by actual representative reconstruction. -/
abbrev FreeCoordinates (P : ∀ v : PairParent T σ, ComplexMarks T σ F v.val)
    (S : ∀ v : FixedParent T σ, StableMarks T σ F v) :=
  ((v : PairParent T σ) → PairedFactor T σ F v (P v)) ×
    ((v : FixedParent T σ) → StableFactor T σ hσ F v (S v))

def coordinatesHomeomorph (P : ∀ v : PairParent T σ, ComplexMarks T σ F v.val)
    (S : ∀ v : FixedParent T σ, StableMarks T σ F v) :
    ShapeSpace T σ F ≃ₜ FreeCoordinates T σ hσ F P S :=
  (orbitHomeomorph T σ hσ F).trans
    ((Homeomorph.piCongrRight fun v => pairedFactorHomeomorph T σ hσ F v (P v)).prodCongr
      (Homeomorph.piCongrRight fun v => fixedFactorHomeomorph T σ hσ F v (S v)))

/-- The complete genuine parameter model: one nonnegative coordinate per free
radial reflection orbit, followed by the explicit finite shape-factor product. -/
def parameterHomeomorph (hF : ReflectedRadiusOrthant.StableFixed T σ F)
    (P : ∀ v : PairParent T σ, ComplexMarks T σ F v.val)
    (S : ∀ v : FixedParent T σ, StableMarks T σ F v) :
    ForestParameterSpace.Space T σ F ≃ₜ
      (ReflectedRadiusCoordinates.Orbit T σ hσ → ℝ≥0) × FreeCoordinates T σ hσ F P S :=
  (ForestParameterProduct.productHomeomorph T σ F hF).trans
    ((ReflectedRadiusCoordinates.coordinatesHomeomorph T σ hσ).prodCongr
      (coordinatesHomeomorph T σ hσ F P S))

open ForestFiniteCoordinateProducts

abbrev StableRealIndex (v : FixedParent T σ) (M : StableMarks T σ F v) : Type _ :=
  letI : DecidableEq (Child T v.val.val) := Classical.decEq _
  match M with
  | .height a _ _ => ReflectedRealIndex
      (ForestNodeShapeCoordinates.HeightFree (Child T v.val.val) (childReflection T σ v) a)
      (ForestNodeShapeCoordinates.heightReflection _ _ (childReflection_involutive T σ hσ v) a)
  | .realPair a b _ ha hb _ => ReflectedRealIndex
      (ForestNodeShapeCoordinates.RealPairFree (Child T v.val.val) a b)
      (ForestNodeShapeCoordinates.realPairReflection _ _ (childReflection_involutive T σ hσ v) a b ha hb)

instance stableRealIndexFintype (v : FixedParent T σ) (M : StableMarks T σ F v) :
    Fintype (StableRealIndex T σ hσ F v M) := by
  cases M <;> unfold StableRealIndex <;> infer_instance

def stableRealHomeomorph (v : FixedParent T σ) (M : StableMarks T σ F v) :
    StableFactor T σ hσ F v M ≃ₜ (StableRealIndex T σ hσ F v M → ℝ) := by
  letI : DecidableEq (Child T v.val.val) := Classical.decEq _
  cases M <;> dsimp only [StableFactor, stableFactorTopology, StableRealIndex]
  all_goals exact reflectedRealHomeomorph _ _

abbrev PairedRealIndex (v : PairParent T σ) (M : ComplexMarks T σ F v.val) :=
  ForestNodeShapeCoordinates.ComplexFree (Child T v.val.val) M.a M.b × Bool

def pairedRealHomeomorph (v : PairParent T σ) (M : ComplexMarks T σ F v.val) :
    PairedFactor T σ F v M ≃ₜ Circle × (PairedRealIndex T σ F v M → ℝ) :=
  (Homeomorph.refl Circle).prodCongr (complexArrayHomeomorph _)

abbrev RealIndex (P : ∀ v : PairParent T σ, ComplexMarks T σ F v.val)
    (S : ∀ v : FixedParent T σ, StableMarks T σ F v) :=
  (Sigma fun v : PairParent T σ => PairedRealIndex T σ F v (P v)) ⊕
    (Sigma fun v : FixedParent T σ => StableRealIndex T σ hσ F v (S v))

/-- All remaining complex coordinates are split into literal real/imaginary
parts, and the finite dependent products are collected into one real vector. -/
def realCoordinatesHomeomorph (P : ∀ v : PairParent T σ, ComplexMarks T σ F v.val)
    (S : ∀ v : FixedParent T σ, StableMarks T σ F v) :
    FreeCoordinates T σ hσ F P S ≃ₜ (PairParent T σ → Circle) × (RealIndex T σ hσ F P S → ℝ) := by
  let hp := (Homeomorph.piCongrRight fun v => pairedRealHomeomorph T σ F v (P v)).trans
    (piProductHomeomorph (PairParent T σ) (fun _ => Circle) (fun v => PairedRealIndex T σ F v (P v) → ℝ))
  let hs := Homeomorph.piCongrRight fun v => stableRealHomeomorph T σ hσ F v (S v)
  let hv := ((sigmaFunctionHomeomorph (PairParent T σ) (fun v => PairedRealIndex T σ F v (P v)) ℝ).prodCongr
    (sigmaFunctionHomeomorph (FixedParent T σ) (fun v => StableRealIndex T σ hσ F v (S v)) ℝ)).trans
      (Homeomorph.sumArrowHomeomorphProdArrow (X := ℝ)).symm
  exact (hp.prodCongr hs).trans
    ((Homeomorph.prodAssoc _ _ _).trans ((Homeomorph.refl (PairParent T σ → Circle)).prodCongr hv))

def shapeRealHomeomorph (P : ∀ v : PairParent T σ, ComplexMarks T σ F v.val)
    (S : ∀ v : FixedParent T σ, StableMarks T σ F v) :
    ShapeSpace T σ F ≃ₜ (PairParent T σ → Circle) × (RealIndex T σ hσ F P S → ℝ) :=
  (coordinatesHomeomorph T σ hσ F P S).trans (realCoordinatesHomeomorph T σ hσ F P S)

/-- A genuine orthant × circle-product × real-vector model of the full closed
normalized parameter space, with no residual reflection/frame equations. -/
def freeParameterHomeomorph (hF : ReflectedRadiusOrthant.StableFixed T σ F)
    (P : ∀ v : PairParent T σ, ComplexMarks T σ F v.val)
    (S : ∀ v : FixedParent T σ, StableMarks T σ F v) :
    ForestParameterSpace.Space T σ F ≃ₜ
      (ReflectedRadiusCoordinates.Orbit T σ hσ → ℝ≥0) ×
        ((PairParent T σ → Circle) × (RealIndex T σ hσ F P S → ℝ)) :=
  (parameterHomeomorph T σ hσ F hF P S).trans
    ((Homeomorph.refl _).prodCongr (realCoordinatesHomeomorph T σ hσ F P S))

def circleCount : ℕ := Fintype.card (PairParent T σ)

def realCount (P : ∀ v : PairParent T σ, ComplexMarks T σ F v.val)
    (S : ∀ v : FixedParent T σ, StableMarks T σ F v) : ℕ := Fintype.card (RealIndex T σ hσ F P S)

/-- Standard finite indices for every coordinate in the actual free model. -/
def finParameterHomeomorph (hF : ReflectedRadiusOrthant.StableFixed T σ F)
    (P : ∀ v : PairParent T σ, ComplexMarks T σ F v.val)
    (S : ∀ v : FixedParent T σ, StableMarks T σ F v) :
    ForestParameterSpace.Space T σ F ≃ₜ
      (Fin (ReflectedRadiusCoordinates.freeRadiusCount T σ hσ) → ℝ≥0) ×
        ((Fin (circleCount T σ) → Circle) × (Fin (realCount T σ hσ F P S) → ℝ)) :=
  (freeParameterHomeomorph T σ hσ F hF P S).trans
    ((Homeomorph.piCongrLeft (Y := fun _ : Fin (ReflectedRadiusCoordinates.freeRadiusCount T σ hσ) => ℝ≥0)
      (Fintype.equivFin _)).prodCongr
      ((Homeomorph.piCongrLeft (Y := fun _ : Fin (circleCount T σ) => Circle) (Fintype.equivFin _)).prodCongr
        (Homeomorph.piCongrLeft (Y := fun _ : Fin (realCount T σ hσ F P S) => ℝ) (Fintype.equivFin _))))

/-- All discrete local marks are constructed from frame compatibility and
actual inhabited-shape metadata; no global factorization is an input. -/
def canonicalParameterHomeomorph (hfixed : ReflectedRadiusOrthant.StableFixed T σ F)
    (hF : ForestMarkedFrameReflection.Compatible T σ F) (hreal : RealPairFixed T σ F)
    (w : ShapeSpace T σ F) :
    ForestParameterSpace.Space T σ F ≃ₜ
      (Fin (ReflectedRadiusCoordinates.freeRadiusCount T σ hσ) → ℝ≥0) ×
        ((Fin (circleCount T σ) → Circle) ×
          (Fin (realCount T σ hσ F (complexMarks T σ F hF) (stableMarks T σ F hF hreal w)) → ℝ)) :=
  finParameterHomeomorph T σ hσ F hfixed (complexMarks T σ F hF) (stableMarks T σ F hF hreal w)

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestShapeCoordinates
