import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterFreeCoordinates
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Orientation

/-! The finite real-cluster model is an explicit radial half-space of the
correct dimension, with its standard product basis and a codimension-one face. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

namespace BoundaryClusterFreeCoordinates

variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)}

theorem finrank_eq (ha : a ∈ S) (hi : i ∉ S) :
    Module.finrank ℝ (BoundaryClusterFreeCoordinates i a S m) = 2 * n + m - 2 := by
  have hS : 0 < S.card := Finset.card_pos.mpr ⟨a, ha⟩
  have hC : 0 < Sᶜ.card := Finset.card_pos.mpr ⟨i, Finset.mem_compl.mpr hi⟩
  rw [Finset.card_compl, Fintype.card_fin] at hC
  have hcards := card_boundaryClusterCoarseIndex_add_shapeIndex i a S hi ha
  simp only [BoundaryClusterFreeCoordinates, Module.finrank_prod, Module.finrank_pi_fintype,
    Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Module.finrank_self, Fintype.card_fin]
  omega

abbrev CoordinateIndex (i a : Fin n) (S : Finset (Fin n)) (m : ℕ) :=
  (Σ _ : BoundaryClusterCoarseIndex i S, Fin 2) ⊕
    (Σ _ : BoundaryClusterShapeIndex a S, Fin 2) ⊕ Fin m ⊕ Unit ⊕ Unit

/-- Real/imaginary coordinates, then boundary coordinates, real center, and radius. -/
def coordinateBasis : Module.Basis (CoordinateIndex i a S m) ℝ (BoundaryClusterFreeCoordinates i a S m) :=
  (Pi.basis (fun _ : BoundaryClusterCoarseIndex i S => Complex.basisOneI)).prod
    ((Pi.basis (fun _ : BoundaryClusterShapeIndex a S => Complex.basisOneI)).prod
      ((Pi.basisFun ℝ (Fin m)).prod
        ((Module.Basis.singleton Unit ℝ).prod (Module.Basis.singleton Unit ℝ))))

def coordinateOrientation :
    Orientation ℝ (BoundaryClusterFreeCoordinates i a S m) (CoordinateIndex i a S m) := by
  classical
  exact coordinateBasis.orientation

def centerProjection : BoundaryClusterFreeCoordinates i a S m →L[ℝ] ℝ where
  toFun := center
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_center

def radiusProjection : BoundaryClusterFreeCoordinates i a S m →L[ℝ] ℝ where
  toFun := radius
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_radius

abbrev FaceCoordinates (i a : Fin n) (S : Finset (Fin n)) (m : ℕ) :=
  (BoundaryClusterCoarseIndex i S → ℂ) × (BoundaryClusterShapeIndex a S → ℂ) × (Fin m → ℝ) × ℝ

def splitRadius : BoundaryClusterFreeCoordinates i a S m ≃ₗ[ℝ] FaceCoordinates i a S m × ℝ where
  toFun x := ((x.1, x.2.1, x.2.2.1, x.2.2.2.1), x.2.2.2.2)
  invFun x := (x.1.1, x.1.2.1, x.1.2.2.1, x.1.2.2.2, x.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def faceEmbedding : FaceCoordinates i a S m →L[ℝ] BoundaryClusterFreeCoordinates i a S m where
  toFun x := (x.1, x.2.1, x.2.2.1, x.2.2.2, 0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  cont := by fun_prop

/-- The boundary face is exactly the kernel of the radial coordinate. -/
theorem range_faceEmbedding :
    LinearMap.range (faceEmbedding (i := i) (a := a) (S := S) (m := m)).toLinearMap =
      LinearMap.ker radiusProjection.toLinearMap := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change (0 : ℝ) = 0
    rfl
  · intro hx
    change x.2.2.2.2 = 0 at hx
    refine ⟨(x.1, x.2.1, x.2.2.1, x.2.2.2.1), ?_⟩
    exact Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl hx.symm)))

theorem finrank_face (ha : a ∈ S) (hi : i ∉ S) :
    Module.finrank ℝ (FaceCoordinates i a S m) = 2 * n + m - 3 := by
  have h : Module.finrank ℝ (BoundaryClusterFreeCoordinates i a S m) =
      Module.finrank ℝ (FaceCoordinates i a S m) + 1 := by
    rw [splitRadius.finrank_eq, Module.finrank_prod, Module.finrank_self]
  rw [finrank_eq ha hi] at h
  omega

end BoundaryClusterFreeCoordinates

namespace BoundaryClusterFreeDomain

open Set Topology

variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

def HalfSpace (i a : Fin n) (S : Finset (Fin n)) (m : ℕ) :=
  {x : BoundaryClusterFreeCoordinates i a S m // 0 ≤ x.radius}

instance : TopologicalSpace (HalfSpace i a S m) :=
  inferInstanceAs (TopologicalSpace {x : BoundaryClusterFreeCoordinates i a S m // 0 ≤ x.radius})

theorem isOpen_in_halfSpace :
    IsOpen {x : HalfSpace i a S m | x.val.OpenConditions l u} :=
  (BoundaryClusterFreeCoordinates.isOpen_openConditions l u).preimage continuous_subtype_val

/-- The exact free admissible domain is an open subset of the radial half-space. -/
def halfSpaceHomeomorph : BoundaryClusterFreeDomain i a S m l u ≃ₜ
    {x : HalfSpace i a S m // x.val.OpenConditions l u} where
  toFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  invFun x := ⟨x.val.val, x.val.property, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Explicit product form of the radial half-space; the face has radius zero. -/
def halfSpaceProductHomeomorph : HalfSpace i a S m ≃ₜ
    BoundaryClusterFreeCoordinates.FaceCoordinates i a S m × Set.Ici (0 : ℝ) where
  toFun x := ((x.val.1, x.val.2.1, x.val.2.2.1, x.val.2.2.2.1), ⟨x.val.2.2.2.2, x.property⟩)
  invFun x := ⟨(x.1.1, x.1.2.1, x.1.2.2.1, x.1.2.2.2, x.2.val), x.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end BoundaryClusterFreeDomain

end EnvelopingIsomorphism.Deformation.Kontsevich
