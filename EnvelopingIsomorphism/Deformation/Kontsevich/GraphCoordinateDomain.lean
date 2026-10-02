import EnvelopingIsomorphism.Deformation.Kontsevich.GraphForms
import EnvelopingIsomorphism.Deformation.Kontsevich.ConfigurationTopology

/-!
# The actual open domain of normalized graph coordinates

The first interior point is fixed at `I`. Admissibility says that all remaining
interior points lie in the upper half plane, all interior points are distinct,
and the real boundary points occur in increasing order. This open coordinate
domain is homeomorphic to the native normalized configuration space.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.GraphForms

open Topology

variable {n m : ℕ}

def Admissible (x : Coordinates n m) : Prop :=
  (∀ j, 0 < (x.1 j).im) ∧
    Function.Injective (fun i => interiorPoint i x) ∧ StrictMono x.2

def admissibleSet (n m : ℕ) : Set (Coordinates n m) := {x | Admissible x}

def CoordinateDomain (n m : ℕ) := {x : Coordinates n m // Admissible x}

instance : TopologicalSpace (CoordinateDomain n m) :=
  inferInstanceAs (TopologicalSpace {x : Coordinates n m // Admissible x})

@[fun_prop] theorem continuous_interiorPoint (i : Fin (n + 1)) :
    Continuous (interiorPoint (m := m) i) :=
  continuous_iff_continuousAt.mpr fun x => (hasFDerivAt_interiorPoint i x).continuousAt

@[fun_prop] theorem continuous_vertexPoint (v : Vertex n m) :
    Continuous (vertexPoint v) :=
  continuous_iff_continuousAt.mpr fun x => (hasFDerivAt_vertexPoint v x).continuousAt

theorem isOpen_admissibleSet (n m : ℕ) : IsOpen (admissibleSet n m) := by
  classical
  have hpos : IsOpen {x : Coordinates n m | ∀ j, 0 < (x.1 j).im} := by
    rw [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_lt continuous_const
      (Complex.continuous_im.comp ((continuous_apply j).comp continuous_fst))
  have hsep : IsOpen {x : Coordinates n m | ∀ i j : Fin (n + 1),
      i ≠ j → interiorPoint i x ≠ interiorPoint j x} := by
    rw [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro i
    rw [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro j
    by_cases hij : i = j
    · simp [hij]
    · simpa [hij, Set.compl_setOf] using
        (isClosed_eq (continuous_interiorPoint (m := m) i)
          (continuous_interiorPoint j)).isOpen_compl
  have hinj : IsOpen {x : Coordinates n m | Function.Injective (fun i => interiorPoint i x)} := by
    convert hsep using 1
    ext x
    constructor
    · intro hx i j hij heq
      exact hij (hx heq)
    · intro hx i j heq
      by_contra hij
      exact hx i j hij heq
  have hboundary : IsOpen {x : Coordinates n m | StrictMono x.2} := by
    change IsOpen {x : Coordinates n m | ∀ i j, i < j → x.2 i < x.2 j}
    rw [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro i
    rw [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro j
    by_cases hij : i < j
    · simpa only [hij, true_implies, Function.comp_def] using
        isOpen_lt ((continuous_apply i).comp (continuous_snd (X := Fin n → ℂ)))
          ((continuous_apply j).comp continuous_snd)
    · simp [hij]
  exact hpos.inter (hinj.inter hboundary)

theorem measurableSet_admissibleSet (n m : ℕ) : MeasurableSet (admissibleSet n m) :=
  (isOpen_admissibleSet n m).measurableSet

theorem Admissible.interiorPoint_im_pos {x : Coordinates n m} (hx : Admissible x)
    (i : Fin (n + 1)) : 0 < (interiorPoint i x).im := by
  cases i using Fin.cases with
  | zero => simp
  | succ j => exact hx.1 j

/-- Native configuration constructed from the displayed coordinate conditions. -/
def toConfiguration (x : CoordinateDomain n m) : Configuration (n + 1) m where
  interior := fun i => ⟨interiorPoint i x.val, x.property.interiorPoint_im_pos i⟩
  boundary := x.val.2
  interior_injective := by
    intro i j hij
    exact x.property.2.1 (congrArg (fun z : UpperHalfPlane => (z : ℂ)) hij)
  boundary_strictMono := x.property.2.2

@[simp] theorem toConfiguration_interior (x : CoordinateDomain n m) (i : Fin (n + 1)) :
    ((toConfiguration x).interior i : ℂ) = interiorPoint i x.val := rfl

@[simp] theorem toConfiguration_boundary (x : CoordinateDomain n m) (j : Fin m) :
    (toConfiguration x).boundary j = x.val.2 j := rfl

@[simp] theorem toConfiguration_vertexPoint (x : CoordinateDomain n m) (v : Vertex n m) :
    (toConfiguration x).vertexPoint v = vertexPoint v x.val := by
  cases v <;> rfl

theorem Admissible.vertexPoint_injective {x : Coordinates n m} (hx : Admissible x) :
    Function.Injective (fun v => vertexPoint v x) := by
  intro v w hvw
  apply (toConfiguration ⟨x, hx⟩).vertexPoint_injective
  simpa only [toConfiguration_vertexPoint] using hvw

def toNormalized (x : CoordinateDomain n m) : Configuration.Normalized (0 : Fin (n + 1)) m :=
  ⟨(toConfiguration x), UpperHalfPlane.ext rfl⟩

@[simp] theorem toNormalized_interior (x : CoordinateDomain n m) (i : Fin (n + 1)) :
    ((toNormalized x).val.interior i : ℂ) = interiorPoint i x.val := rfl

@[simp] theorem toNormalized_boundary (x : CoordinateDomain n m) (j : Fin m) :
    (toNormalized x).val.boundary j = x.val.2 j := rfl

@[fun_prop] theorem continuous_toConfiguration :
    Continuous (toConfiguration : CoordinateDomain n m → Configuration (n + 1) m) := by
  apply Configuration.isEmbedding_vertexCoordinates.isInducing.continuous_iff.mpr
  apply continuous_pi
  intro v
  simp only [Function.comp_def, toConfiguration_vertexPoint]
  exact (continuous_vertexPoint v).comp continuous_subtype_val

@[fun_prop] theorem continuous_toNormalized :
    Continuous (toNormalized : CoordinateDomain n m → Configuration.Normalized (0 : Fin (n + 1)) m) :=
  continuous_toConfiguration.subtype_mk _

/-- The inverse simply forgets the fixed first interior coordinate. -/
def fromNormalized (c : Configuration.Normalized (0 : Fin (n + 1)) m) : Coordinates n m :=
  (fun j => (c.val.interior j.succ : ℂ), c.val.boundary)

@[simp] theorem fromNormalized_fst (c : Configuration.Normalized (0 : Fin (n + 1)) m)
    (j : Fin n) : (fromNormalized c).1 j = (c.val.interior j.succ : ℂ) := rfl

@[simp] theorem fromNormalized_snd (c : Configuration.Normalized (0 : Fin (n + 1)) m)
    (j : Fin m) : (fromNormalized c).2 j = c.val.boundary j := rfl

@[simp] theorem interiorPoint_fromNormalized (c : Configuration.Normalized (0 : Fin (n + 1)) m)
    (i : Fin (n + 1)) : interiorPoint i (fromNormalized c) = (c.val.interior i : ℂ) := by
  cases i using Fin.cases with
  | zero => exact (congrArg (fun z : UpperHalfPlane => (z : ℂ)) c.property).symm
  | succ j => rfl

@[simp] theorem vertexPoint_fromNormalized (c : Configuration.Normalized (0 : Fin (n + 1)) m)
    (v : Vertex n m) : vertexPoint v (fromNormalized c) = c.val.vertexPoint v := by
  cases v with
  | inl i => exact interiorPoint_fromNormalized c i
  | inr j => rfl

theorem fromNormalized_admissible (c : Configuration.Normalized (0 : Fin (n + 1)) m) :
    Admissible (fromNormalized c) := by
  refine ⟨fun j => (c.val.interior j.succ).im_pos, ?_, c.val.boundary_strictMono⟩
  intro i j hij
  dsimp only at hij
  rw [interiorPoint_fromNormalized, interiorPoint_fromNormalized] at hij
  exact c.val.interior_injective (UpperHalfPlane.ext hij)

def fromNormalizedDomain (c : Configuration.Normalized (0 : Fin (n + 1)) m) : CoordinateDomain n m :=
  ⟨fromNormalized c, fromNormalized_admissible c⟩

@[fun_prop] theorem continuous_fromNormalized :
    Continuous (fromNormalized : Configuration.Normalized (0 : Fin (n + 1)) m → Coordinates n m) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro j
    exact (Configuration.continuous_vertexCoordinate (Sum.inl j.succ)).comp continuous_subtype_val
  · apply continuous_pi
    intro j
    exact Complex.continuous_re.comp
      ((Configuration.continuous_vertexCoordinate (Sum.inr j)).comp continuous_subtype_val)

@[fun_prop] theorem continuous_fromNormalizedDomain :
    Continuous (fromNormalizedDomain : Configuration.Normalized (0 : Fin (n + 1)) m →
      CoordinateDomain n m) := continuous_fromNormalized.subtype_mk _

@[simp] theorem fromNormalized_toNormalized (x : CoordinateDomain n m) :
    fromNormalized (toNormalized x) = x.val := by
  apply Prod.ext
  · funext j
    rfl
  · rfl

@[simp] theorem fromNormalizedDomain_toNormalized (x : CoordinateDomain n m) :
    fromNormalizedDomain (toNormalized x) = x :=
  Subtype.ext (fromNormalized_toNormalized x)

@[simp] theorem toNormalized_fromNormalizedDomain
    (c : Configuration.Normalized (0 : Fin (n + 1)) m) :
    toNormalized (fromNormalizedDomain c) = c := by
  apply Subtype.ext
  apply Configuration.ext
  · funext i
    apply UpperHalfPlane.ext
    exact interiorPoint_fromNormalized c i
  · rfl

/-- The actual open graph coordinate domain parametrizes the native normalized configurations. -/
def coordinateHomeomorph (n m : ℕ) :
    CoordinateDomain n m ≃ₜ Configuration.Normalized (0 : Fin (n + 1)) m where
  toFun := toNormalized
  invFun := fromNormalizedDomain
  left_inv := fromNormalizedDomain_toNormalized
  right_inv := toNormalized_fromNormalizedDomain
  continuous_toFun := continuous_toNormalized
  continuous_invFun := continuous_fromNormalizedDomain

@[simp] theorem coordinateHomeomorph_apply (x : CoordinateDomain n m) :
    coordinateHomeomorph n m x = toNormalized x := rfl

@[simp] theorem coordinateHomeomorph_symm_apply
    (c : Configuration.Normalized (0 : Fin (n + 1)) m) :
    (coordinateHomeomorph n m).symm c = fromNormalizedDomain c := rfl

theorem range_fromNormalized :
    Set.range (fromNormalized : Configuration.Normalized (0 : Fin (n + 1)) m → Coordinates n m) =
      admissibleSet n m := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    exact fromNormalized_admissible c
  · intro hx
    exact ⟨toNormalized ⟨x, hx⟩, fromNormalized_toNormalized ⟨x, hx⟩⟩

/-- The coordinate inverse is an actual open embedding into the raw vector space. -/
theorem isOpenEmbedding_fromNormalized :
    IsOpenEmbedding (fromNormalized : Configuration.Normalized (0 : Fin (n + 1)) m →
      Coordinates n m) := by
  have h := (isOpen_admissibleSet n m).isOpenEmbedding_subtypeVal.comp
    (coordinateHomeomorph n m).symm.isOpenEmbedding
  exact h

/-- With a single interior vertex, no interior restrictions remain in the raw coordinates. -/
@[simp] theorem admissible_zero_iff (x : Coordinates 0 m) : Admissible x ↔ StrictMono x.2 := by
  constructor
  · exact fun hx => hx.2.2
  · intro hx
    exact ⟨fun j => Fin.elim0 j, fun i j _ => (Fin.eq_zero i).trans (Fin.eq_zero j).symm, hx⟩

theorem admissibleSet_zero (m : ℕ) :
    admissibleSet 0 m = {x : Coordinates 0 m | StrictMono x.2} := by
  ext x
  exact admissible_zero_iff x

end EnvelopingIsomorphism.Deformation.Kontsevich.GraphForms
