import EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedShapeCoordinates
import Mathlib.Analysis.Complex.Circle

/-! Actual normalized single-node shape factors. These models retain the circle
direction of complex frames and the conjugation signs of stable frames. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestNodeShapeCoordinates

open ComplexConjugate
open scoped Classical Topology

section Complex

variable (A : Type*) (a b : A) (hab : a ≠ b)

abbrev ComplexFree := {u : A // u ≠ a ∧ u ≠ b}
abbrev ComplexShape := {q : A → ℂ // q a = 0 ∧ ‖q b‖ = 1}

/-- Raw remaining coordinates are retained, as in the native cluster free-coordinate model. -/
def complexCoordinates (q : ComplexShape A a b) : Circle × (ComplexFree A a b → ℂ) :=
  (⟨q.val b, mem_sphere_zero_iff_norm.mpr q.property.2⟩, fun u => q.val u.val)

def complexRestore (c : Circle × (ComplexFree A a b → ℂ)) (u : A) : ℂ :=
  if hua : u = a then 0 else if hub : u = b then (c.1 : ℂ) else c.2 ⟨u, hua, hub⟩

@[simp] theorem complexRestore_anchor (c : Circle × (ComplexFree A a b → ℂ)) :
    complexRestore A a b c a = 0 := by simp [complexRestore]

include hab in
@[simp] theorem complexRestore_reference (c : Circle × (ComplexFree A a b → ℂ)) :
    complexRestore A a b c b = (c.1 : ℂ) := by simp [complexRestore, hab.symm]

@[simp] theorem complexRestore_free (c : Circle × (ComplexFree A a b → ℂ)) (u : ComplexFree A a b) :
    complexRestore A a b c u.val = c.2 u := by
  simp only [complexRestore, dif_neg u.property.1, dif_neg u.property.2]

def complexOfCoordinates (c : Circle × (ComplexFree A a b → ℂ)) : ComplexShape A a b :=
  ⟨complexRestore A a b c, complexRestore_anchor A a b c,
    by rw [complexRestore_reference A a b hab]; exact c.1.norm_coe⟩

theorem complexOfCoordinates_coordinates (q : ComplexShape A a b) :
    complexOfCoordinates A a b hab (complexCoordinates A a b q) = q := by
  apply Subtype.ext
  funext u
  change complexRestore A a b (complexCoordinates A a b q) u = q.val u
  by_cases hua : u = a
  · subst u
    rw [complexRestore_anchor, q.property.1]
  · by_cases hub : u = b
    · subst u
      exact complexRestore_reference A a b hab _
    · exact complexRestore_free A a b _ ⟨u, hua, hub⟩

theorem complexCoordinates_ofCoordinates (c : Circle × (ComplexFree A a b → ℂ)) :
    complexCoordinates A a b (complexOfCoordinates A a b hab c) = c := by
  apply Prod.ext
  · apply Circle.ext
    exact complexRestore_reference A a b hab c
  · funext u
    exact complexRestore_free A a b c u

theorem continuous_complexCoordinates : Continuous (complexCoordinates A a b) := by
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    exact (continuous_apply b).comp continuous_subtype_val
  · apply continuous_pi
    intro u
    exact (continuous_apply u.val).comp continuous_subtype_val

theorem continuous_complexOfCoordinates : Continuous (complexOfCoordinates A a b hab) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro u
  change Continuous (fun c => complexRestore A a b c u)
  unfold complexRestore
  split_ifs <;> fun_prop

/-- Genuine node shape coordinates: the second mark gives Circle, not a fixed phase. -/
def complexHomeomorph : ComplexShape A a b ≃ₜ Circle × (ComplexFree A a b → ℂ) where
  toEquiv :=
    { toFun := complexCoordinates A a b
      invFun := complexOfCoordinates A a b hab
      left_inv := complexOfCoordinates_coordinates A a b hab
      right_inv := complexCoordinates_ofCoordinates A a b hab }
  continuous_toFun := continuous_complexCoordinates A a b
  continuous_invFun := continuous_complexOfCoordinates A a b hab

end Complex

section Height

variable (A : Type*) (σ : A → A) (hσ : Function.Involutive σ) (a : A) (ha : σ a ≠ a)

abbrev HeightFree := {u : A // u ≠ a ∧ u ≠ σ a}
abbrev StableHeightShape := {q : A → ℂ // (∀ u, q (σ u) = conj (q u)) ∧ q a = Complex.I}

/-- An actual normalized reflected height shape itself certifies that its mark is nonfixed. -/
theorem height_anchor_nonfixed (q : StableHeightShape A σ a) : σ a ≠ a := by
  intro h
  have hi := congrArg Complex.im (q.property.1 a)
  simp [h, q.property.2] at hi
  norm_num at hi

/-- The actual reflection on the remaining labels after removing the marked conjugate pair. -/
def heightReflection (u : HeightFree A σ a) : HeightFree A σ a :=
  ⟨σ u.val,
    (fun h => u.property.2 ((hσ u.val).symm.trans (congrArg σ h))),
    (fun h => u.property.1 (hσ.injective h))⟩

theorem heightReflection_involutive : Function.Involutive (heightReflection A σ hσ a) := by
  intro u
  exact Subtype.ext (hσ u.val)

abbrev HeightRemaining := ReflectedShapeCoordinates.Space (HeightFree A σ a) (heightReflection A σ hσ a)

def heightRestrict (q : StableHeightShape A σ a) : HeightRemaining A σ hσ a :=
  ⟨fun u => q.val u.val, fun u => q.property.1 u.val⟩

/-- The height mark is I and its reflected mate is exactly -I. -/
def heightRestore (q : HeightRemaining A σ hσ a) (u : A) : ℂ :=
  if hua : u = a then Complex.I else if hub : u = σ a then -Complex.I else q.val ⟨u, hua, hub⟩

@[simp] theorem heightRestore_anchor (q : HeightRemaining A σ hσ a) :
    heightRestore A σ hσ a q a = Complex.I := by simp [heightRestore]

include ha in
@[simp] theorem heightRestore_reflected_anchor (q : HeightRemaining A σ hσ a) :
    heightRestore A σ hσ a q (σ a) = -Complex.I := by simp [heightRestore, ha]

@[simp] theorem heightRestore_free (q : HeightRemaining A σ hσ a) (u : HeightFree A σ a) :
    heightRestore A σ hσ a q u.val = q.val u := by
  simp only [heightRestore, dif_neg u.property.1, dif_neg u.property.2]

include ha in
theorem heightRestore_reflection (q : HeightRemaining A σ hσ a) (u : A) :
    heightRestore A σ hσ a q (σ u) = conj (heightRestore A σ hσ a q u) := by
  by_cases hua : u = a
  · subst u
    rw [heightRestore_anchor, heightRestore_reflected_anchor A σ hσ a ha]
    simp
  · by_cases hub : u = σ a
    · subst u
      rw [hσ a, heightRestore_anchor, heightRestore_reflected_anchor A σ hσ a ha]
      simp
    · have hsu := (heightReflection A σ hσ a ⟨u, hua, hub⟩).property
      change σ u ≠ a ∧ σ u ≠ σ a at hsu
      simp only [heightRestore, dif_neg hua, dif_neg hub, dif_neg hsu.1, dif_neg hsu.2]
      exact q.property ⟨u, hua, hub⟩

def heightOfRemaining (q : HeightRemaining A σ hσ a) : StableHeightShape A σ a :=
  ⟨heightRestore A σ hσ a q, heightRestore_reflection A σ hσ a ha q,
    heightRestore_anchor A σ hσ a q⟩

theorem heightOfRemaining_restrict (q : StableHeightShape A σ a) :
    heightOfRemaining A σ hσ a ha (heightRestrict A σ hσ a q) = q := by
  apply Subtype.ext
  funext u
  change heightRestore A σ hσ a (heightRestrict A σ hσ a q) u = q.val u
  by_cases hua : u = a
  · subst u
    rw [heightRestore_anchor, q.property.2]
  · by_cases hub : u = σ a
    · subst u
      rw [heightRestore_reflected_anchor A σ hσ a ha, q.property.1 a, q.property.2]
      simp
    · exact heightRestore_free A σ hσ a _ ⟨u, hua, hub⟩

theorem heightRestrict_ofRemaining (q : HeightRemaining A σ hσ a) :
    heightRestrict A σ hσ a (heightOfRemaining A σ hσ a ha q) = q := by
  apply Subtype.ext
  funext u
  exact heightRestore_free A σ hσ a q u

theorem continuous_heightRestrict : Continuous (heightRestrict A σ hσ a) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro u
  exact (continuous_apply u.val).comp continuous_subtype_val

theorem continuous_heightOfRemaining : Continuous (heightOfRemaining A σ hσ a ha) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro u
  change Continuous (fun q => heightRestore A σ hσ a q u)
  unfold heightRestore
  split_ifs
  · exact continuous_const
  · exact continuous_const
  · exact (continuous_apply _).comp continuous_subtype_val

/-- Removing the marked pair is an actual homeomorphism of normalized reflected arrays. -/
def heightRestrictionHomeomorph : StableHeightShape A σ a ≃ₜ HeightRemaining A σ hσ a where
  toEquiv :=
    { toFun := heightRestrict A σ hσ a
      invFun := heightOfRemaining A σ hσ a ha
      left_inv := heightOfRemaining_restrict A σ hσ a ha
      right_inv := heightRestrict_ofRemaining A σ hσ a ha }
  continuous_toFun := continuous_heightRestrict A σ hσ a
  continuous_invFun := continuous_heightOfRemaining A σ hσ a ha

/-- Stable-height node factors have complex free pair coordinates and real fixed coordinates. -/
def heightHomeomorph [Fintype A] : StableHeightShape A σ a ≃ₜ
    ReflectedShapeCoordinates.Coordinates (HeightFree A σ a) (heightReflection A σ hσ a) :=
  (heightRestrictionHomeomorph A σ hσ a ha).trans
    (ReflectedShapeCoordinates.coordinatesHomeomorph _ _ (heightReflection_involutive A σ hσ a))

end Height

section RealPair

variable (A : Type*) (σ : A → A) (hσ : Function.Involutive σ)
    (a b : A) (hab : a ≠ b) (ha : σ a = a) (hb : σ b = b)

abbrev RealPairFree := {u : A // u ≠ a ∧ u ≠ b}
abbrev StableRealPairShape :=
  {q : A → ℂ // (∀ u, q (σ u) = conj (q u)) ∧ q a = 0 ∧ q b = 1}

/-- The actual reflection on labels remaining after removing two fixed real marks. -/
def realPairReflection (u : RealPairFree A a b) : RealPairFree A a b :=
  ⟨σ u.val, (fun h => u.property.1 (hσ.injective (h.trans ha.symm))),
    (fun h => u.property.2 (hσ.injective (h.trans hb.symm)))⟩

theorem realPairReflection_involutive : Function.Involutive (realPairReflection A σ hσ a b ha hb) := by
  intro u
  exact Subtype.ext (hσ u.val)

abbrev RealPairRemaining :=
  ReflectedShapeCoordinates.Space (RealPairFree A a b) (realPairReflection A σ hσ a b ha hb)

def realPairRestrict (q : StableRealPairShape A σ a b) : RealPairRemaining A σ hσ a b ha hb :=
  ⟨fun u => q.val u.val, fun u => q.property.1 u.val⟩

/-- The ordered real frame convention fixes the first mark to 0 and the second to +1. -/
def realPairRestore (q : RealPairRemaining A σ hσ a b ha hb) (u : A) : ℂ :=
  if hua : u = a then 0 else if hub : u = b then 1 else q.val ⟨u, hua, hub⟩

@[simp] theorem realPairRestore_anchor (q : RealPairRemaining A σ hσ a b ha hb) :
    realPairRestore A σ hσ a b ha hb q a = 0 := by simp [realPairRestore]

include hab in
@[simp] theorem realPairRestore_reference (q : RealPairRemaining A σ hσ a b ha hb) :
    realPairRestore A σ hσ a b ha hb q b = 1 := by simp [realPairRestore, hab.symm]

@[simp] theorem realPairRestore_free (q : RealPairRemaining A σ hσ a b ha hb) (u : RealPairFree A a b) :
    realPairRestore A σ hσ a b ha hb q u.val = q.val u := by
  simp only [realPairRestore, dif_neg u.property.1, dif_neg u.property.2]

include hab in
theorem realPairRestore_reflection (q : RealPairRemaining A σ hσ a b ha hb) (u : A) :
    realPairRestore A σ hσ a b ha hb q (σ u) = conj (realPairRestore A σ hσ a b ha hb q u) := by
  by_cases hua : u = a
  · subst u
    rw [ha, realPairRestore_anchor]
    simp
  · by_cases hub : u = b
    · subst u
      rw [hb, realPairRestore_reference A σ hσ a b hab ha hb]
      simp
    · have hsu := (realPairReflection A σ hσ a b ha hb ⟨u, hua, hub⟩).property
      change σ u ≠ a ∧ σ u ≠ b at hsu
      simp only [realPairRestore, dif_neg hua, dif_neg hub, dif_neg hsu.1, dif_neg hsu.2]
      exact q.property ⟨u, hua, hub⟩

def realPairOfRemaining (q : RealPairRemaining A σ hσ a b ha hb) : StableRealPairShape A σ a b :=
  ⟨realPairRestore A σ hσ a b ha hb q, realPairRestore_reflection A σ hσ a b hab ha hb q,
    realPairRestore_anchor A σ hσ a b ha hb q, realPairRestore_reference A σ hσ a b hab ha hb q⟩

theorem realPairOfRemaining_restrict (q : StableRealPairShape A σ a b) :
    realPairOfRemaining A σ hσ a b hab ha hb (realPairRestrict A σ hσ a b ha hb q) = q := by
  apply Subtype.ext
  funext u
  change realPairRestore A σ hσ a b ha hb (realPairRestrict A σ hσ a b ha hb q) u = q.val u
  by_cases hua : u = a
  · subst u
    rw [realPairRestore_anchor, q.property.2.1]
  · by_cases hub : u = b
    · subst u
      rw [realPairRestore_reference A σ hσ a b hab ha hb, q.property.2.2]
    · exact realPairRestore_free A σ hσ a b ha hb _ ⟨u, hua, hub⟩

theorem realPairRestrict_ofRemaining (q : RealPairRemaining A σ hσ a b ha hb) :
    realPairRestrict A σ hσ a b ha hb (realPairOfRemaining A σ hσ a b hab ha hb q) = q := by
  apply Subtype.ext
  funext u
  exact realPairRestore_free A σ hσ a b ha hb q u

theorem continuous_realPairRestrict : Continuous (realPairRestrict A σ hσ a b ha hb) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro u
  exact (continuous_apply u.val).comp continuous_subtype_val

theorem continuous_realPairOfRemaining : Continuous (realPairOfRemaining A σ hσ a b hab ha hb) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro u
  change Continuous (fun q => realPairRestore A σ hσ a b ha hb q u)
  unfold realPairRestore
  split_ifs
  · exact continuous_const
  · exact continuous_const
  · exact (continuous_apply _).comp continuous_subtype_val

/-- Removing the fixed real marks is a genuine homeomorphism of normalized arrays. -/
def realPairRestrictionHomeomorph : StableRealPairShape A σ a b ≃ₜ RealPairRemaining A σ hσ a b ha hb where
  toEquiv :=
    { toFun := realPairRestrict A σ hσ a b ha hb
      invFun := realPairOfRemaining A σ hσ a b hab ha hb
      left_inv := realPairOfRemaining_restrict A σ hσ a b hab ha hb
      right_inv := realPairRestrict_ofRemaining A σ hσ a b hab ha hb }
  continuous_toFun := continuous_realPairRestrict A σ hσ a b ha hb
  continuous_invFun := continuous_realPairOfRemaining A σ hσ a b hab ha hb

/-- Stable real-pair node factors have exactly the remaining real and complex orbit coordinates. -/
def realPairHomeomorph [Fintype A] : StableRealPairShape A σ a b ≃ₜ
    ReflectedShapeCoordinates.Coordinates (RealPairFree A a b) (realPairReflection A σ hσ a b ha hb) :=
  (realPairRestrictionHomeomorph A σ hσ a b hab ha hb).trans
    (ReflectedShapeCoordinates.coordinatesHomeomorph _ _ (realPairReflection_involutive A σ hσ a b ha hb))

end RealPair

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestNodeShapeCoordinates
