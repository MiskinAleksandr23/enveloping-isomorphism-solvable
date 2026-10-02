import EnvelopingIsomorphism.Deformation.Kontsevich.Compactification

/-!
# Full direction and ratio data, independently of the normalization anchor

All distinct doubled-pair directions and all admissible doubled-triple ratios
are retained. Only compactified position entries are forgotten. These data are
invariant under the actual positive affine action, so all interior-anchor
normalizations have exactly the same encoded range and compact closure.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration ComplexConjugate Topology Set

variable {n m : ℕ}

/-- The full direction and ratio coordinates; triple targets may coincide,
exactly as in the original `DoubledTriple` index type. -/
abbrev DRData (n m : ℕ) :=
  (DoubledPair n m → Circle) × (DoubledTriple n m → Set.Icc (0 : ℝ) 1)

instance : CompactSpace (DRData n m) := by infer_instance
instance : T2Space (DRData n m) := by infer_instance

/-- Forget only compactified positions from the original full encoder. -/
def projectDR : CompactCoordinateSpace n m → DRData n m := Prod.snd

@[simp] theorem projectDR_apply (x : CompactCoordinateSpace n m) : projectDR x = x.2 := rfl

@[fun_prop] theorem continuous_projectDR : Continuous (projectDR (n := n) (m := m)) :=
  continuous_snd

/-- The same full direction/ratio encoder on unnormalized configurations. -/
def directionRatioCoordinates (c : Configuration n m) : DRData n m :=
  (fun p ↦ complexPhase (c.pairDifference p), fun t ↦ c.tripleDistanceRatio t)

@[fun_prop] theorem continuous_directionRatioCoordinates :
    Continuous (directionRatioCoordinates : Configuration n m → DRData n m) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro p
    apply continuous_iff_continuousAt.mpr
    intro c
    exact (continuousAt_complexPhase (c.pairDifference_ne_zero p)).comp
      (f := fun d : Configuration n m ↦ d.pairDifference p) (x := c)
      (continuous_pairDifference p).continuousAt
  · exact continuous_pi fun t ↦ continuous_tripleDistanceRatio t

namespace Configuration

/-- Conjugate interior points obey the same real affine transformation as the original points. -/
theorem act_doubledPoint (g : PositiveAffine) (c : Configuration n m) (v : DoubledLabel n m) :
    (act g c).doubledPoint v = (g.scale : ℂ) * c.doubledPoint v + (g.shift : ℂ) := by
  cases v with
  | inl v => exact act_vertexPoint g c v
  | inr i =>
    change conj ((g.onUpper (c.interior i) : UpperHalfPlane) : ℂ) = _
    rw [PositiveAffine.coe_onUpper]
    simp only [map_add, map_mul, Complex.conj_ofReal, doubledPoint]

/-- Every actual doubled-pair difference scales by the same positive real number. -/
theorem act_pairDifference (g : PositiveAffine) (c : Configuration n m) (p : DoubledPair n m) :
    (act g c).pairDifference p = (g.scale : ℂ) * c.pairDifference p := by
  rw [pairDifference, act_doubledPoint, act_doubledPoint, pairDifference]
  ring

theorem norm_act_pairDifference (g : PositiveAffine) (c : Configuration n m) (p : DoubledPair n m) :
    ‖(act g c).pairDifference p‖ = g.scale * ‖c.pairDifference p‖ := by
  rw [act_pairDifference, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos g.scale_pos]

/-- Positive real scaling cancels in every full doubled-triple ratio. -/
theorem act_tripleDistanceRatio (g : PositiveAffine) (c : Configuration n m) (t : DoubledTriple n m) :
    (act g c).tripleDistanceRatio t = c.tripleDistanceRatio t := by
  apply Subtype.ext
  change ‖(act g c).pairDifference _‖ /
      (‖(act g c).pairDifference _‖ + ‖(act g c).pairDifference _‖) =
    ‖c.pairDifference _‖ / (‖c.pairDifference _‖ + ‖c.pairDifference _‖)
  simp only [norm_act_pairDifference]
  rw [← mul_add]
  exact mul_div_mul_left _ _ g.scale_pos.ne'

end Configuration

/-- The full encoder, including all triple ratios, is affine invariant. -/
theorem directionRatioCoordinates_act (g : PositiveAffine) (c : Configuration n m) :
    directionRatioCoordinates (act g c) = directionRatioCoordinates c := by
  apply Prod.ext
  · funext p
    change complexPhase ((act g c).pairDifference p) = complexPhase (c.pairDifference p)
    rw [act_pairDifference, complexPhase_pos_real_mul g.scale_pos]
  · funext t
    exact act_tripleDistanceRatio g c t

theorem directionRatioCoordinates_affineRelated {c e : Configuration n m}
    (h : AffineRelated c e) : directionRatioCoordinates c = directionRatioCoordinates e := by
  obtain ⟨g, rfl⟩ := h
  exact (directionRatioCoordinates_act g c).symm

@[simp] theorem directionRatioCoordinates_normalize (i : Fin n) (c : Configuration n m) :
    directionRatioCoordinates (normalize i c) = directionRatioCoordinates c :=
  directionRatioCoordinates_act (normalizer i c) c

def normalizedDirectionRatios {i : Fin n} (c : Normalized i m) : DRData n m :=
  directionRatioCoordinates c.val

@[fun_prop] theorem continuous_normalizedDirectionRatios (i : Fin n) :
    Continuous (normalizedDirectionRatios : Normalized i m → DRData n m) :=
  continuous_directionRatioCoordinates.comp continuous_subtype_val

@[simp] theorem projectDR_compactCoordinates {i : Fin n} (c : Normalized i m) :
    projectDR (compactCoordinates c) = normalizedDirectionRatios c := rfl

@[simp] theorem normalizedDirectionRatios_normalized (i : Fin n) (c : Configuration n m) :
    normalizedDirectionRatios (normalized i c) = directionRatioCoordinates c :=
  directionRatioCoordinates_normalize i c

/-- Every affine representative has the same encoded data as its normalization at any anchor. -/
theorem range_normalizedDirectionRatios_eq_configuration (i : Fin n) :
    Set.range (normalizedDirectionRatios : Normalized i m → DRData n m) =
      Set.range (directionRatioCoordinates : Configuration n m → DRData n m) := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c.val, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨normalized i c, normalizedDirectionRatios_normalized i c⟩

/-- The full projected ranges coincide for any two interior normalization anchors. -/
theorem range_normalizedDirectionRatios_eq (i j : Fin n) :
    Set.range (normalizedDirectionRatios : Normalized i m → DRData n m) =
      Set.range (normalizedDirectionRatios : Normalized j m → DRData n m) := by
  rw [range_normalizedDirectionRatios_eq_configuration,
    range_normalizedDirectionRatios_eq_configuration]

theorem range_projectDR_compactCoordinates_eq (i j : Fin n) :
    Set.range (projectDR ∘ (compactCoordinates : Normalized i m → CompactCoordinateSpace n m)) =
      Set.range (projectDR ∘ (compactCoordinates : Normalized j m → CompactCoordinateSpace n m)) :=
  range_normalizedDirectionRatios_eq i j

/-- The common compact-closure set is defined without selecting an anchor. -/
def directionRatioSet (n m : ℕ) : Set (DRData n m) :=
  closure (Set.range (directionRatioCoordinates : Configuration n m → DRData n m))

theorem directionRatioSet_eq_normalized (i : Fin n) :
    directionRatioSet n m =
      closure (Set.range (normalizedDirectionRatios : Normalized i m → DRData n m)) := by
  rw [range_normalizedDirectionRatios_eq_configuration]
  rfl

theorem directionRatioSet_eq_projected (i : Fin n) :
    directionRatioSet n m =
      closure (Set.range (projectDR ∘
        (compactCoordinates : Normalized i m → CompactCoordinateSpace n m))) :=
  directionRatioSet_eq_normalized i

/-- The anchor-independent compact space of full direction and ratio data. -/
def DRSpace (n m : ℕ) := directionRatioSet n m

instance : TopologicalSpace (DRSpace n m) :=
  inferInstanceAs (TopologicalSpace (directionRatioSet n m))

instance : CompactSpace (DRSpace n m) :=
  isCompact_iff_compactSpace.mp isClosed_closure.isCompact

instance : T2Space (DRSpace n m) :=
  inferInstanceAs (T2Space (directionRatioSet n m))

end EnvelopingIsomorphism.Deformation.Kontsevich
