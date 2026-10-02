import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterFreeCoordinates
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Orientation

/-! The free pure-boundary cluster coordinates form the correct-dimensional
radial half-space, with an explicit basis and a genuine codimension-one face. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

namespace PureBoundaryClusterFreeCoordinates

variable {n m : ℕ} {i : Fin n} {a b : Fin m}

theorem finrank_eq (hab : a ≠ b) :
    Module.finrank ℝ (PureBoundaryClusterFreeCoordinates i m a b) = 2 * n + m - 2 := by
  have hn : 1 ≤ n := by have := i.isLt; omega
  have hm : 2 ≤ m := by
    by_contra h
    have ha := a.isLt
    have hb := b.isLt
    exact hab (Fin.ext (by omega))
  simp only [PureBoundaryClusterFreeCoordinates, Module.finrank_prod,
    Module.finrank_pi_fintype, Complex.finrank_real_complex, Module.finrank_self,
    Finset.sum_const, Finset.card_univ, smul_eq_mul,
    card_pureBoundaryInteriorIndex, card_pureBoundaryFreeIndex a b hab]
  omega

abbrev CoordinateIndex (i : Fin n) (m : ℕ) (a b : Fin m) :=
  (Σ _ : PureBoundaryInteriorIndex i, Fin 2) ⊕ PureBoundaryFreeIndex a b ⊕ Unit ⊕ Unit

/-- Real/imaginary interior coordinates, free boundary slots, center, and radius. -/
def coordinateBasis : Module.Basis (CoordinateIndex i m a b) ℝ (PureBoundaryClusterFreeCoordinates i m a b) :=
  (Pi.basis (fun _ : PureBoundaryInteriorIndex i => Complex.basisOneI)).prod
    ((Pi.basisFun ℝ (PureBoundaryFreeIndex a b)).prod
      ((Module.Basis.singleton Unit ℝ).prod (Module.Basis.singleton Unit ℝ)))

def coordinateOrientation :
    Orientation ℝ (PureBoundaryClusterFreeCoordinates i m a b) (CoordinateIndex i m a b) := by
  classical
  exact coordinateBasis.orientation

def centerProjection : PureBoundaryClusterFreeCoordinates i m a b →L[ℝ] ℝ where
  toFun := center
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_center

def radiusProjection : PureBoundaryClusterFreeCoordinates i m a b →L[ℝ] ℝ where
  toFun := radius
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_radius

abbrev FaceCoordinates (i : Fin n) (m : ℕ) (a b : Fin m) :=
  (PureBoundaryInteriorIndex i → ℂ) × (PureBoundaryFreeIndex a b → ℝ) × ℝ

def splitRadius : PureBoundaryClusterFreeCoordinates i m a b ≃ₗ[ℝ] FaceCoordinates i m a b × ℝ where
  toFun x := ((x.1, x.2.1, x.2.2.1), x.2.2.2)
  invFun x := (x.1.1, x.1.2.1, x.1.2.2, x.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def faceEmbedding : FaceCoordinates i m a b →L[ℝ] PureBoundaryClusterFreeCoordinates i m a b where
  toFun x := (x.1, x.2.1, x.2.2, 0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  cont := by fun_prop

@[simp] theorem radius_faceEmbedding (x : FaceCoordinates i m a b) : (faceEmbedding x).radius = 0 := rfl

theorem faceEmbedding_splitRadius (x : PureBoundaryClusterFreeCoordinates i m a b) (hx : x.radius = 0) :
    faceEmbedding (splitRadius x).1 = x :=
  Prod.ext rfl (Prod.ext rfl (Prod.ext rfl hx.symm))

theorem range_faceEmbedding :
    LinearMap.range (faceEmbedding (i := i) (a := a) (b := b)).toLinearMap =
      LinearMap.ker radiusProjection.toLinearMap := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro hx
    exact ⟨(splitRadius x).1, faceEmbedding_splitRadius x hx⟩

theorem finrank_face (hab : a ≠ b) :
    Module.finrank ℝ (FaceCoordinates i m a b) = 2 * n + m - 3 := by
  have h : Module.finrank ℝ (PureBoundaryClusterFreeCoordinates i m a b) =
      Module.finrank ℝ (FaceCoordinates i m a b) + 1 := by
    rw [splitRadius.finrank_eq, Module.finrank_prod, Module.finrank_self]
  rw [finrank_eq hab] at h
  omega

end PureBoundaryClusterFreeCoordinates

namespace PureBoundaryClusterFreeDomain

open Set Topology

variable {n m : ℕ} {i : Fin n} {l u : Fin (m + 1)} {a b : Fin m}

def HalfSpace (i : Fin n) (m : ℕ) (a b : Fin m) :=
  {x : PureBoundaryClusterFreeCoordinates i m a b // 0 ≤ x.radius}

instance : TopologicalSpace (HalfSpace i m a b) :=
  inferInstanceAs (TopologicalSpace {x : PureBoundaryClusterFreeCoordinates i m a b // 0 ≤ x.radius})

theorem isOpen_in_halfSpace :
    IsOpen {x : HalfSpace i m a b | x.val.OpenConditions l u} :=
  (PureBoundaryClusterFreeCoordinates.isOpen_openConditions l u).preimage continuous_subtype_val

/-- The actual admissible free domain is an open subset of the radial half-space. -/
def halfSpaceHomeomorph : PureBoundaryClusterFreeDomain i m l u a b ≃ₜ
    {x : HalfSpace i m a b // x.val.OpenConditions l u} where
  toFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  invFun x := ⟨x.val.val, x.val.property, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Explicit product decomposition into face coordinates and nonnegative radius. -/
def halfSpaceProductHomeomorph : HalfSpace i m a b ≃ₜ
    PureBoundaryClusterFreeCoordinates.FaceCoordinates i m a b × Set.Ici (0 : ℝ) where
  toFun x := ((x.val.1, x.val.2.1, x.val.2.2.1), ⟨x.val.2.2.2, x.property⟩)
  invFun x := ⟨(x.1.1, x.1.2.1, x.1.2.2, x.2.val), x.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end PureBoundaryClusterFreeDomain

end EnvelopingIsomorphism.Deformation.Kontsevich
