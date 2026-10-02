import EnvelopingIsomorphism.Deformation.Kontsevich.GraphFormsClosed
import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterData
import EnvelopingIsomorphism.Deformation.Kontsevich.AlternatingRankVanishing
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Actual forms on a pure external collision face

Interior coordinates are stationary. Boundary coordinates in the block are
`center + radius * shape`; the two endpoint shapes are fixed at zero and one.
The zero-radius face map is proved to factor through the coarse coordinates.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterForms

open GraphForms ContinuousAlternatingMap Module
open scoped Topology

variable {n m : ℕ}

abbrev Outside (S : Finset (Fin m)) := {j : Fin m // j ∉ S}
abbrev Inner (S : Finset (Fin m)) (a b : Fin m) := {j : Fin m // j ∈ (S.erase a).erase b}
abbrev Coarse (n : ℕ) (S : Finset (Fin m)) := (Fin n → ℂ) × (ℝ × (Outside S → ℝ))
abbrev Shape (S : Finset (Fin m)) (a b : Fin m) := Inner S a b → ℝ
abbrev Face (n : ℕ) (S : Finset (Fin m)) (a b : Fin m) := Coarse n S × Shape S a b
abbrev Ambient (n : ℕ) (S : Finset (Fin m)) (a b : Fin m) := ℝ × Face n S a b

def centerCLM (S : Finset (Fin m)) : Coarse n S →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ (Outside S → ℝ)).comp
    (ContinuousLinearMap.snd ℝ (Fin n → ℂ) (ℝ × (Outside S → ℝ)))

def outsideCLM (S : Finset (Fin m)) (j : Outside S) : Coarse n S →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j).comp ((ContinuousLinearMap.snd ℝ ℝ (Outside S → ℝ)).comp
    (ContinuousLinearMap.snd ℝ (Fin n → ℂ) (ℝ × (Outside S → ℝ))))

def boundaryBaseCLM (S : Finset (Fin m)) (j : Fin m) : Coarse n S →L[ℝ] ℝ :=
  if hj : j ∈ S then centerCLM S else outsideCLM S ⟨j, hj⟩

def coarseMap (S : Finset (Fin m)) : Coarse n S →L[ℝ] Coordinates n m :=
  (ContinuousLinearMap.fst ℝ (Fin n → ℂ) (ℝ × (Outside S → ℝ))).prod
    (ContinuousLinearMap.pi (boundaryBaseCLM S))

def shapeVelocity (S : Finset (Fin m)) (a b : Fin m) (β : Shape S a b) (j : Fin m) : ℝ :=
  if hj : j ∈ S then
    if hja : j = a then 0 else if hjb : j = b then 1 else
      β ⟨j, by simp [Finset.mem_erase, hj, hja, hjb]⟩
  else 0

theorem contDiff_shapeVelocity (S : Finset (Fin m)) (a b : Fin m) :
    ContDiff ℝ ⊤ (shapeVelocity S a b) := by
  apply contDiff_pi.mpr
  intro j
  unfold shapeVelocity
  split_ifs <;> fun_prop

/-- The actual normalized graph coordinates at arbitrary real radius. -/
def scaledMap (S : Finset (Fin m)) (a b : Fin m) (p : Ambient n S a b) : Coordinates n m :=
  coarseMap S p.2.1 + p.1 • (0, shapeVelocity S a b p.2.2)

theorem contDiff_scaledMap (S : Finset (Fin m)) (a b : Fin m) :
    ContDiff ℝ ⊤ (scaledMap (n := n) S a b) :=
  ((coarseMap S).contDiff.comp (contDiff_fst.comp contDiff_snd)).add
    (contDiff_fst.smul (contDiff_const.prodMk
      ((contDiff_shapeVelocity S a b).comp (contDiff_snd.comp contDiff_snd))))

@[simp] theorem interiorPoint_scaledMap (S : Finset (Fin m)) (a b : Fin m)
    (p : Ambient n S a b) (i : Fin (n + 1)) :
    interiorPoint i (scaledMap S a b p) = interiorPoint i (coarseMap S p.2.1) := by
  cases i using Fin.cases <;> simp [scaledMap, interiorPoint]

/-- Only the internal vertices must remain distinct and in the upper half plane.
Collisions among real external coordinates are allowed. -/
def InteriorRegular (x : Coordinates n m) : Prop :=
  (∀ i, 0 < (interiorPoint i x).im) ∧ Function.Injective (fun i => interiorPoint i x)

theorem InteriorRegular.scaledMap {S : Finset (Fin m)} {a b : Fin m} {p : Ambient n S a b}
    (h : InteriorRegular (coarseMap S p.2.1)) : InteriorRegular (scaledMap S a b p) := by
  constructor
  · intro i
    simpa only [interiorPoint_scaledMap] using h.1 i
  · intro i j hij
    apply h.2
    simpa only [interiorPoint_scaledMap] using hij

theorem InteriorRegular.edge_endpoints {x : Coordinates n m} (hx : InteriorRegular x)
    (e : Edge n m) (he : e.target ≠ Sum.inl e.source) :
    (edgeMap e x).2 - star (edgeMap e x).1 ≠ 0 ∧ edgeRatio e x ≠ 0 := by
  have hp := hx.1 e.source
  have hq : 0 ≤ (vertexPoint e.target x).im := by
    cases ht : e.target with
    | inl j => exact (hx.1 j).le
    | inr j => simp [vertexPoint]
  have hne : vertexPoint e.target x ≠ interiorPoint e.source x := by
    cases ht : e.target with
    | inl j =>
        intro h
        exact he (ht.trans (congrArg Sum.inl (hx.2 h)))
    | inr j =>
        intro h
        have hi := congrArg Complex.im h
        simp only [vertexPoint, Complex.ofReal_im] at hi
        exact hp.ne' hi.symm
  exact ⟨harmonicDenominator_ne_zero hp hq, harmonicRatio_ne_zero hp hq hne⟩

theorem contDiffAt_edgeForm_of_interiorRegular {x : Coordinates n m} (hx : InteriorRegular x)
    (e : Edge n m) (he : e.target ≠ Sum.inl e.source) : ContDiffAt ℝ ⊤ (edgeForm e) x := by
  obtain ⟨hd, hr⟩ := hx.edge_endpoints e he
  have hω := contDiffAt_harmonicAngleForm (edgeMap e x).1 (edgeMap e x).2 hd hr
  exact (ContinuousAlternatingMap.compContinuousLinearMapCLM (edgeTangent e)).contDiff.contDiffAt.comp x
    (hω.comp x (contDiff_edgeMap e).contDiffAt)

theorem contDiffAt_edgeLinear_of_interiorRegular {x : Coordinates n m} (hx : InteriorRegular x)
    (e : Edge n m) (he : e.target ≠ Sum.inl e.source) : ContDiffAt ℝ ⊤ (edgeLinear e) x := by
  change ContDiffAt ℝ ⊤ (fun y =>
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := Coordinates n m) (F := ℝ)
      (0 : Fin 1)).symm (edgeForm e y)) x
  exact (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := Coordinates n m) (F := ℝ)
    (0 : Fin 1)).symm.contDiff.contDiffAt.comp x (contDiffAt_edgeForm_of_interiorRegular hx e he)

def faceInclusion (S : Finset (Fin m)) (a b : Fin m) : Face n S a b →L[ℝ] Ambient n S a b :=
  (0 : Face n S a b →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ _)

def faceMap (S : Finset (Fin m)) (a b : Fin m) (y : Face n S a b) : Coordinates n m :=
  scaledMap S a b (faceInclusion S a b y)

theorem faceMap_eq_coarse (S : Finset (Fin m)) (a b : Fin m) :
    faceMap (n := n) S a b = fun y => coarseMap S y.1 := by
  funext y
  simp [faceMap, scaledMap, faceInclusion]

theorem fderiv_faceMap (S : Finset (Fin m)) (a b : Fin m) (y : Face n S a b) :
    fderiv ℝ (faceMap S a b) y = (coarseMap S).comp
      (ContinuousLinearMap.fst ℝ (Coarse n S) (Shape S a b)) := by
  rw [faceMap_eq_coarse]
  exact ((coarseMap S).comp (ContinuousLinearMap.fst ℝ (Coarse n S) (Shape S a b))).fderiv

def scaledGraphForm {r : ℕ} (S : Finset (Fin m)) (a b : Fin m)
    (edges : Fin r → Edge n m) (p : Ambient n S a b) :
    Ambient n S a b [⋀^Fin r]→L[ℝ] ℝ :=
  (topForm edges (scaledMap S a b p)).compContinuousLinearMap (fderiv ℝ (scaledMap S a b) p)

def faceGraphForm {r : ℕ} (S : Finset (Fin m)) (a b : Fin m)
    (edges : Fin r → Edge n m) (y : Face n S a b) :
    Face n S a b [⋀^Fin r]→L[ℝ] ℝ :=
  (topForm edges (faceMap S a b y)).compContinuousLinearMap (fderiv ℝ (faceMap S a b) y)

def coarseGraphForm {r : ℕ} (S : Finset (Fin m)) (edges : Fin r → Edge n m)
    (c : Coarse n S) : Coarse n S [⋀^Fin r]→L[ℝ] ℝ :=
  (topForm edges (coarseMap S c)).compContinuousLinearMap (coarseMap S)

/-- Smoothness through radius zero is actual ambient smoothness of the pulled
back graph form. No distinctness among real boundary points is needed. -/
theorem contDiffAt_scaledGraphForm {r : ℕ} (S : Finset (Fin m)) (a b : Fin m)
    (edges : Fin r → Edge n m) (he : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    {p : Ambient n S a b} (hreg : InteriorRegular (coarseMap S p.2.1)) :
    ContDiffAt ℝ ⊤ (scaledGraphForm S a b edges) p := by
  have hlin : ContDiffAt ℝ ⊤ (fun q : Ambient n S a b =>
      fun j => edgeLinear (edges j) (scaledMap S a b q)) p :=
    contDiffAt_pi.mpr fun j =>
      (contDiffAt_edgeLinear_of_interiorRegular hreg.scaledMap (edges j) (he j)).comp p
        (contDiff_scaledMap S a b).contDiffAt
  have hpi : ContDiffAt ℝ ⊤ (fun q : Ambient n S a b =>
      ContinuousLinearMap.pi fun j => edgeLinear (edges j) (scaledMap S a b q)) p :=
    (ContinuousLinearMap.piEquivL ℝ (Coordinates n m) (fun _ : Fin r => ℝ)).contDiff.contDiffAt.comp p hlin
  have hder : ContDiffAt ℝ ⊤ (fderiv ℝ (scaledMap (n := n) S a b)) p :=
    (contDiff_scaledMap S a b).contDiffAt.fderiv_right (by simp)
  have hcomp := hpi.clm_comp hder
  have heq : scaledGraphForm S a b edges = fun q : Ambient n S a b =>
      (coordinateVolume r).compContinuousLinearMap
        ((ContinuousLinearMap.pi fun j => edgeLinear (edges j) (scaledMap S a b q)).comp
          (fderiv ℝ (scaledMap S a b) q)) := by
    funext q
    ext v
    rfl
  rw [heq]
  exact (contDiff_compContinuousLinearMap (coordinateVolume r)).contDiffAt.comp p hcomp

def scaledEdgeForm (S : Finset (Fin m)) (a b : Fin m) (e : Edge n m) (p : Ambient n S a b) :
    Ambient n S a b [⋀^Fin 1]→L[ℝ] ℝ :=
  (edgeForm e (scaledMap S a b p)).compContinuousLinearMap (fderiv ℝ (scaledMap S a b) p)

def faceEdgeForm (S : Finset (Fin m)) (a b : Fin m) (e : Edge n m) (y : Face n S a b) :
    Face n S a b [⋀^Fin 1]→L[ℝ] ℝ :=
  (edgeForm e (faceMap S a b y)).compContinuousLinearMap (fderiv ℝ (faceMap S a b) y)

def coarseEdgeForm (S : Finset (Fin m)) (e : Edge n m) (c : Coarse n S) :
    Coarse n S [⋀^Fin 1]→L[ℝ] ℝ :=
  (edgeForm e (coarseMap S c)).compContinuousLinearMap (coarseMap S)

theorem scaledEdgeForm_eq_harmonicPullback (S : Finset (Fin m)) (a b : Fin m)
    (e : Edge n m) (p : Ambient n S a b) :
    scaledEdgeForm S a b e p =
      (harmonicAngleForm (edgeMap e (scaledMap S a b p))).compContinuousLinearMap
        (fderiv ℝ (edgeMap e ∘ scaledMap S a b) p) := by
  rw [fderiv_comp p (hasFDerivAt_edgeMap e (scaledMap S a b p)).differentiableAt
    ((contDiff_scaledMap S a b).contDiffAt.differentiableAt (by simp)),
    (hasFDerivAt_edgeMap e (scaledMap S a b p)).fderiv]
  ext v
  rfl

theorem faceEdgeForm_eq_restriction (S : Finset (Fin m)) (a b : Fin m)
    (e : Edge n m) (y : Face n S a b) :
    faceEdgeForm S a b e y =
      (scaledEdgeForm S a b e (faceInclusion S a b y)).compContinuousLinearMap
        (faceInclusion S a b) := by
  have hder := fderiv_comp y
    ((contDiff_scaledMap S a b).contDiffAt.differentiableAt (by simp))
    (faceInclusion S a b).differentiableAt
  change (edgeForm e (faceMap S a b y)).compContinuousLinearMap
    (fderiv ℝ (scaledMap S a b ∘ faceInclusion S a b) y) = _
  rw [hder, (faceInclusion S a b).fderiv]
  ext v
  rfl

theorem topForm_single_edge (e : Edge n m) (x : Coordinates n m) :
    topForm (fun _ : Fin 1 => e) x = edgeForm e x := by
  ext v
  rw [topForm_apply, Matrix.det_unique]
  change edgeForm e x (fun _ : Fin 1 => v 0) = edgeForm e x v
  congr 1
  funext i
  exact congrArg v (Subsingleton.elim 0 i)

theorem contDiffAt_scaledEdgeForm (S : Finset (Fin m)) (a b : Fin m)
    (e : Edge n m) (he : e.target ≠ Sum.inl e.source)
    {p : Ambient n S a b} (hreg : InteriorRegular (coarseMap S p.2.1)) :
    ContDiffAt ℝ ⊤ (scaledEdgeForm S a b e) p := by
  have heq : scaledEdgeForm S a b e = scaledGraphForm S a b (fun _ : Fin 1 => e) := by
    funext q
    rw [scaledGraphForm, topForm_single_edge]
    rfl
  rw [heq]
  exact contDiffAt_scaledGraphForm S a b (fun _ : Fin 1 => e) (fun _ => he) hreg

theorem faceEdgeForm_eq_coarse_pullback (S : Finset (Fin m)) (a b : Fin m)
    (e : Edge n m) (y : Face n S a b) :
    faceEdgeForm S a b e y = (coarseEdgeForm S e y.1).compContinuousLinearMap
      (ContinuousLinearMap.fst ℝ (Coarse n S) (Shape S a b)) := by
  rw [faceEdgeForm, fderiv_faceMap, faceMap_eq_coarse]
  ext v
  rfl

/-- The face form is the actual restriction of the smooth radius-dependent pullback. -/
theorem faceGraphForm_eq_restriction {r : ℕ} (S : Finset (Fin m)) (a b : Fin m)
    (edges : Fin r → Edge n m) (y : Face n S a b) :
    faceGraphForm S a b edges y =
      (scaledGraphForm S a b edges (faceInclusion S a b y)).compContinuousLinearMap
        (faceInclusion S a b) := by
  have hder := fderiv_comp y
    ((contDiff_scaledMap S a b).contDiffAt.differentiableAt (by simp))
    (faceInclusion S a b).differentiableAt
  change fderiv ℝ (scaledMap S a b ∘ faceInclusion S a b) y = _ at hder
  change (topForm edges (faceMap S a b y)).compContinuousLinearMap
    (fderiv ℝ (scaledMap S a b ∘ faceInclusion S a b) y) = _
  rw [hder, (faceInclusion S a b).fderiv]
  ext v
  rfl

theorem contDiffAt_faceGraphForm {r : ℕ} (S : Finset (Fin m)) (a b : Fin m)
    (edges : Fin r → Edge n m) (he : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    {y : Face n S a b} (hreg : InteriorRegular (coarseMap S y.1)) :
    ContDiffAt ℝ ⊤ (faceGraphForm S a b edges) y := by
  have heq : faceGraphForm S a b edges = fun z =>
      (scaledGraphForm S a b edges (faceInclusion S a b z)).compContinuousLinearMap
        (faceInclusion S a b) := funext (faceGraphForm_eq_restriction S a b edges)
  rw [heq]
  exact (ContinuousAlternatingMap.compContinuousLinearMapCLM (faceInclusion S a b)).contDiff.contDiffAt.comp y
    ((contDiffAt_scaledGraphForm S a b edges he hreg).comp y (faceInclusion S a b).contDiff.contDiffAt)

/-- Proven factorization: at zero radius the form depends only on the coarse
coordinates and is pulled back along the coarse projection. -/
theorem faceGraphForm_eq_coarse_pullback {r : ℕ} (S : Finset (Fin m)) (a b : Fin m)
    (edges : Fin r → Edge n m) (y : Face n S a b) :
    faceGraphForm S a b edges y = (coarseGraphForm S edges y.1).compContinuousLinearMap
      (ContinuousLinearMap.fst ℝ (Coarse n S) (Shape S a b)) := by
  rw [faceGraphForm, fderiv_faceMap, faceMap_eq_coarse]
  ext v
  rfl

theorem faceGraphForm_eq_zero_of_coarse_dimension_lt {r : ℕ} (S : Finset (Fin m)) (a b : Fin m)
    (edges : Fin r → Edge n m) (hr : Module.finrank ℝ (Coarse n S) < r) (y : Face n S a b) :
    faceGraphForm S a b edges y = 0 := by
  rw [faceGraphForm_eq_coarse_pullback]
  exact continuousAlternating_fst_pullback_eq_zero_of_finrank_lt _ hr

theorem faceGraphForm_restrict_coarse {r : ℕ} (S : Finset (Fin m)) (a b : Fin m)
    (edges : Fin r → Edge n m) (y : Face n S a b) :
    (faceGraphForm S a b edges y).compContinuousLinearMap
      ((ContinuousLinearMap.id ℝ (Coarse n S)).prod (0 : Coarse n S →L[ℝ] Shape S a b)) =
        coarseGraphForm S edges y.1 := by
  rw [faceGraphForm_eq_coarse_pullback]
  ext v
  rfl

theorem card_outside (S : Finset (Fin m)) : Fintype.card (Outside S) = m - S.card := by
  simp [Outside]

theorem card_inner (S : Finset (Fin m)) (a b : Fin m)
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) : Fintype.card (Inner S a b) = S.card - 2 := by
  change Fintype.card {j : Fin m // j ∈ (S.erase a).erase b} = _
  rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hab.symm, hb⟩),
    Finset.card_erase_of_mem ha]
  omega

theorem finrank_coarse (S : Finset (Fin m)) :
    Module.finrank ℝ (Coarse n S) = n * 2 + 1 + (m - S.card) := by
  simp [Coarse, Module.finrank_prod, Module.finrank_pi_fintype, Nat.add_assoc]

theorem finrank_shape (S : Finset (Fin m)) (a b : Fin m)
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    Module.finrank ℝ (Shape S a b) = S.card - 2 := by
  change Module.finrank ℝ (Inner S a b → ℝ) = _
  rw [Module.finrank_pi, card_inner S a b ha hb hab]

theorem finrank_face (S : Finset (Fin m)) (a b : Fin m)
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    Module.finrank ℝ (Face n S a b) = n * 2 + m - 1 := by
  change Module.finrank ℝ (Coarse n S × Shape S a b) = _
  rw [Module.finrank_prod, finrank_coarse, finrank_shape S a b ha hb hab]
  have hcard : S.card ≤ m := by simpa using S.card_le_univ
  have htwo : 2 ≤ S.card := Finset.one_lt_card.mpr ⟨a, ha, b, hb, hab⟩
  omega

/-- A block of at least three external points has a free internal shape
coordinate. The actual full-face-degree graph form therefore vanishes. -/
theorem faceGraphForm_fullDegree_eq_zero_of_card_ge_three (S : Finset (Fin m)) (a b : Fin m)
    (hS : 3 ≤ S.card) (edges : Fin (n * 2 + m - 1) → Edge n m) (y : Face n S a b) :
    faceGraphForm S a b edges y = 0 := by
  apply faceGraphForm_eq_zero_of_coarse_dimension_lt
  rw [finrank_coarse]
  have hcard : S.card ≤ m := by simpa using S.card_le_univ
  omega

/-- For a two-point block the shape space is a point, and the face is actually
linearly equivalent to its coarse coordinate space. -/
def twoPointFaceEquiv (S : Finset (Fin m)) (a b : Fin m)
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (hS : S.card = 2) :
    Face n S a b ≃L[ℝ] Coarse n S := by
  have hzero : Module.finrank ℝ (Shape S a b) = 0 := by rw [finrank_shape S a b ha hb hab, hS]
  letI : Subsingleton (Shape S a b) := Module.finrank_zero_iff.mp hzero
  exact
    { toFun := Prod.fst
      invFun := fun c => (c, 0)
      left_inv := fun y => Prod.ext rfl (Subsingleton.elim _ _)
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      continuous_toFun := continuous_fst
      continuous_invFun := continuous_id.prodMk continuous_const }

/-- The two-point face retains the actual coarse form, rather than vanishing.
This is the local form factor appearing in the ordinary multiplication face. -/
theorem twoPoint_faceGraphForm_eq_coarse {r : ℕ} (S : Finset (Fin m)) (a b : Fin m)
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (hS : S.card = 2)
    (edges : Fin r → Edge n m) (y : Face n S a b) :
    faceGraphForm S a b edges y = (coarseGraphForm S edges y.1).compContinuousLinearMap
      (twoPointFaceEquiv S a b ha hb hab hS).toContinuousLinearMap :=
  faceGraphForm_eq_coarse_pullback S a b edges y

section ActualData

variable {l u : Fin (m + 1)} {a b : Fin m}

def dataCoarse (D : PureBoundaryClusterData (0 : Fin (n + 1)) m l u a b) :
    Coarse n (boundaryClusterBlock l u) :=
  (fun j => (D.interior j.succ : ℂ), (D.center, fun j => D.boundaryBase j.val))

def dataShape (D : PureBoundaryClusterData (0 : Fin (n + 1)) m l u a b) :
    Shape (boundaryClusterBlock l u) a b := fun j => D.boundaryVelocity j.val

theorem coarseMap_dataCoarse (D : PureBoundaryClusterData (0 : Fin (n + 1)) m l u a b) :
    coarseMap (boundaryClusterBlock l u) (dataCoarse D) =
      (fun j => (D.interior j.succ : ℂ), D.boundaryBase) := by
  apply Prod.ext
  · rfl
  · funext j
    change (boundaryBaseCLM (boundaryClusterBlock l u) j) (dataCoarse D) = D.boundaryBase j
    rw [boundaryBaseCLM]
    split_ifs with hj
    · exact (D.boundaryBase_eq_center j hj).symm
    · rfl

theorem shapeVelocity_dataShape (D : PureBoundaryClusterData (0 : Fin (n + 1)) m l u a b) :
    shapeVelocity (boundaryClusterBlock l u) a b (dataShape D) = D.boundaryVelocity := by
  funext j
  by_cases hj : j ∈ boundaryClusterBlock l u
  · by_cases hja : j = a
    · subst j
      simp [shapeVelocity, D.left_mem, D.boundaryVelocity_left]
    · by_cases hjb : j = b
      · subst j
        simp [shapeVelocity, D.right_mem, hja, D.boundaryVelocity_right]
      · simp [shapeVelocity, hj, hja, hjb, dataShape]
  · simp [shapeVelocity, hj, D.boundaryVelocity_zero_off j hj]

theorem scaledMap_data (D : PureBoundaryClusterData (0 : Fin (n + 1)) m l u a b) (r : ℝ) :
    scaledMap (boundaryClusterBlock l u) a b (r, (dataCoarse D, dataShape D)) =
      (fun j => (D.interior j.succ : ℂ), D.scaledBoundary r) := by
  rw [scaledMap, coarseMap_dataCoarse, shapeVelocity_dataShape]
  apply Prod.ext
  · simp
  · rfl

/-- The free frame at positive radius is the actual normalized configuration
already constructed from the collision datum. -/
theorem scaledMap_data_eq_fromNormalized
    (D : PureBoundaryClusterData (0 : Fin (n + 1)) m l u a b) {ε r : ℝ}
    (hε : D.IsSafeScale ε) (hr : 0 < r) (hrε : r ≤ ε) :
    scaledMap (boundaryClusterBlock l u) a b (r, (dataCoarse D, dataShape D)) =
      GraphForms.fromNormalized (D.normalized hε hr hrε) := by
  rw [scaledMap_data]
  rfl

theorem dataCoarse_regular (D : PureBoundaryClusterData (0 : Fin (n + 1)) m l u a b) :
    InteriorRegular (coarseMap (boundaryClusterBlock l u) (dataCoarse D)) := by
  have hi (j : Fin (n + 1)) : interiorPoint j (coarseMap (boundaryClusterBlock l u) (dataCoarse D)) =
      (D.interior j : ℂ) := by
    cases j using Fin.cases with
    | zero => exact (congrArg (fun z : UpperHalfPlane => (z : ℂ)) D.interior_normalized).symm
    | succ j => rfl
  constructor
  · intro j
    rw [hi]
    exact (D.interior j).im_pos
  · intro j k hjk
    apply D.interior_injective
    apply UpperHalfPlane.ext
    simpa only [hi] using hjk

theorem contDiffAt_scaledGraphForm_data {r : ℕ}
    (D : PureBoundaryClusterData (0 : Fin (n + 1)) m l u a b)
    (edges : Fin r → Edge n m) (he : ∀ j, (edges j).target ≠ Sum.inl (edges j).source) (ρ : ℝ) :
    ContDiffAt ℝ ⊤ (scaledGraphForm (boundaryClusterBlock l u) a b edges)
      (ρ, (dataCoarse D, dataShape D)) :=
  contDiffAt_scaledGraphForm (boundaryClusterBlock l u) a b edges he (dataCoarse_regular D)

theorem faceGraphForm_data_eq_zero_of_block_card_ge_three
    (D : PureBoundaryClusterData (0 : Fin (n + 1)) m l u a b)
    (hS : 3 ≤ (boundaryClusterBlock l u).card) (edges : Fin (n * 2 + m - 1) → Edge n m) :
    faceGraphForm (boundaryClusterBlock l u) a b edges (dataCoarse D, dataShape D) = 0 :=
  faceGraphForm_fullDegree_eq_zero_of_card_ge_three (boundaryClusterBlock l u) a b hS edges _

end ActualData

end EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterForms
