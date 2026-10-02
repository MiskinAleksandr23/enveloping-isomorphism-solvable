import EnvelopingIsomorphism.Deformation.Gauge.GraphTaylorCoefficients
import EnvelopingIsomorphism.Deformation.GeneralGraphInsertionLow

/-! Uniform binary-source graphs, including no internal vertices, with genuine
legacy compatibility and concatenation under actual admissible graph grafting. -/
noncomputable section
namespace EnvelopingIsomorphism.Deformation.UniformBinaryGraphs
open KontsevichGraph.General
open scoped BigOperators Classical

abbrev BinaryGraph (n m : ℕ) := Graph (fun _ : Fin n ↦ 2) m

variable {n m : ℕ}

/-- The two-boundary general graph retains precisely the legacy targets. -/
def toLegacy (Γ : BinaryGraph n 2) : KontsevichGraph n where
  target e := Γ.target ⟨e.1,e.2⟩
  noLoops := Γ.noLoops
  distinctTargets v h := by
    have he := Γ.distinctTargets v h
    exact (by decide : (0 : Fin 2) ≠ 1) he

@[simp] theorem ofBinary_toLegacy (Γ : BinaryGraph n 2) : ofBinary (toLegacy Γ) = Γ := by
  apply Graph.ext
  rfl

@[simp] theorem toLegacy_ofBinary (Γ : KontsevichGraph n) : toLegacy (ofBinary Γ) = Γ := by
  apply KontsevichGraph.ext
  rfl

/-- An actual equivalence of admissible graph structures; no graph is quotiented. -/
def legacyEquiv (n : ℕ) : BinaryGraph n 2 ≃ KontsevichGraph n where
  toFun := toLegacy
  invFun := ofBinary
  left_inv := ofBinary_toLegacy
  right_inv := toLegacy_ofBinary

@[simp] theorem legacyEquiv_symm_apply (Γ : KontsevichGraph n) : (legacyEquiv n).symm Γ = ofBinary Γ := rfl

def emptyGraph (m : ℕ) : BinaryGraph 0 m where
  target e := Fin.elim0 e.1
  noLoops v := Fin.elim0 v
  distinctTargets v := Fin.elim0 v

instance emptyGraphUnique (m : ℕ) : Unique (BinaryGraph 0 m) where
  default := emptyGraph m
  uniq Γ := by
    apply Graph.ext
    funext e
    exact Fin.elim0 e.1

section Operators
variable {R : Type*} [CommRing R] {d : ℕ}

/-- Full cochains obtained from the genuine polynomial bivector tensors. -/
def operator (Γ : BinaryGraph n m) :
    MultilinearMap R (fun _ : Fin n ↦ Multiderivation R (MvPolynomial (Fin d) R) 2)
      (Cochain R (MvPolynomial (Fin d) R) m) :=
  Γ.cochainOperator.compLinearMap (fun _ ↦ Gauge.GraphTaylorCoefficients.coordinateTensor)

@[simp] theorem operator_apply (Γ : BinaryGraph n m)
    (F : Fin n → Multiderivation R (MvPolynomial (Fin d) R) 2) :
    operator Γ F = Γ.cochainOperator (fun v ↦ Gauge.GraphTaylorCoefficients.coordinateTensor (F v)) := rfl

theorem operator_ofBinary (Γ : KontsevichGraph n)
    (F : Fin n → Multiderivation R (MvPolynomial (Fin d) R) 2) :
    operator (ofBinary Γ) F = (cochainTwoEquiv R (MvPolynomial (Fin d) R)).symm
      (Gauge.GraphTaylorCoefficients.graphCoefficient Γ F) := by
  rw [Gauge.GraphTaylorCoefficients.graphCoefficient_apply, LinearEquiv.symm_apply_apply]
  rfl

theorem operator_legacy (Γ : BinaryGraph n 2)
    (F : Fin n → Multiderivation R (MvPolynomial (Fin d) R) 2) :
    cochainTwoEquiv R (MvPolynomial (Fin d) R) (operator Γ F) =
      Gauge.GraphTaylorCoefficients.graphCoefficient (legacyEquiv n Γ) F := by
  rw [Gauge.GraphTaylorCoefficients.graphCoefficient_apply]
  change _ = cochainTwoEquiv R (MvPolynomial (Fin d) R)
    ((ofBinary (toLegacy Γ)).cochainOperator _)
  rw [ofBinary_toLegacy]
  rfl

/-- With no internal graph vertices every exterior factor is retained, including
nullary multiplication. -/
theorem operator_emptyGraph (F : Fin 0 → Multiderivation R (MvPolynomial (Fin d) R) 2)
    (f : Fin m → MvPolynomial (Fin d) R) : operator (emptyGraph m) F f = ∏ j, f j :=
  Graph.cochainOperator_no_internal _ _ _

theorem operator_emptyGraph_two (F : Fin 0 → Multiderivation R (MvPolynomial (Fin d) R) 2) :
    cochainTwoEquiv R (MvPolynomial (Fin d) R) (operator (emptyGraph 2) F) =
      LinearMap.mul R (MvPolynomial (Fin d) R) := by
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro g
  change operator (emptyGraph 2) F ![f,g] = f*g
  rw [operator_emptyGraph, Fin.prod_univ_two]
  rfl
end Operators

section ArityTransport
variable {R : Type*} [CommRing R] {d : ℕ} {q q' : Fin n → ℕ}

def castGraph (h : q = q') (Γ : Graph q m) : Graph q' m := h ▸ Γ

theorem castGraph_target (h : q = q') (Γ : Graph q m) (v : Fin n) (j : Fin (q' v)) :
    (castGraph h Γ).target ⟨v,j⟩ = Γ.target ⟨v,Fin.cast (congrFun h v).symm j⟩ := by
  cases h
  rfl

def castTensors (h : q = q') (T : (v : Fin n) → Tensor (q v) d R) :
    (v : Fin n) → Tensor (q' v) d R := h ▸ T

theorem castTensors_apply (h : q = q') (T : (v : Fin n) → Tensor (q v) d R)
    (v : Fin n) (a : Fin (q' v) → Fin d) :
    castTensors h T v a = T v (fun j ↦ a (Fin.cast (congrFun h v) j)) := by
  cases h
  rfl

theorem cochainOperator_castGraph (h : q = q') (Γ : Graph q m)
    (T : (v : Fin n) → Tensor (q v) d R) :
    (castGraph h Γ).cochainOperator (castTensors h T) = Γ.cochainOperator T := by
  cases h
  rfl
end ArityTransport

variable {a b : ℕ}

theorem graftArity_two : graftArity (fun _ : Fin a ↦ 2) (fun _ : Fin b ↦ 2) =
    fun _ : Fin (a+b) ↦ 2 := by
  funext v
  refine Fin.addCases (fun v ↦ ?_) (fun v ↦ ?_) v <;> simp

/-- Actual incoming-arrow choices of the general admissible graft. -/
abbrev GraftChoices (Γ : BinaryGraph a 2) (r : Fin 2) := Γ.GraftChoices (b := b) (l := 1) r

/-- Concatenate the binary arities and keep the actual admissible graph targets. -/
def uniformGraft (Γ : BinaryGraph a 2) (Δ : BinaryGraph b 2) (r : Fin 2)
    (χ : GraftChoices (b := b) Γ r) : BinaryGraph (a+b) 3 :=
  castGraph graftArity_two (Γ.graft Δ r χ)

theorem uniformGraft_target (Γ : BinaryGraph a 2) (Δ : BinaryGraph b 2) (r : Fin 2)
    (χ : GraftChoices (b := b) Γ r) (v : Fin (a+b)) (j : Fin 2) :
    (uniformGraft Γ Δ r χ).target ⟨v,j⟩ =
      (Γ.graft Δ r χ).target ⟨v,Fin.cast (congrFun graftArity_two v).symm j⟩ :=
  castGraph_target graftArity_two _ _ _

section GraftOperators
variable {R : Type*} [CommRing R] {d : ℕ}

def uniformGraftTensors (T : Fin a → Tensor 2 d R) (U : Fin b → Tensor 2 d R) :
    Fin (a+b) → Tensor 2 d R :=
  castTensors graftArity_two (graftTensors (fun _ ↦ 2) (fun _ ↦ 2) T U)

theorem uniformGraftTensors_eq_addCases (T : Fin a → Tensor 2 d R) (U : Fin b → Tensor 2 d R) :
    uniformGraftTensors T U = Fin.addCases T U := by
  funext v lab
  rw [uniformGraftTensors, castTensors_apply]
  refine Fin.addCases (fun v ↦ ?_) (fun v ↦ ?_) v
  · rw [graftTensors_outer]
    simp only [Fin.addCases_left]
    congr 1
  · rw [graftTensors_inner]
    simp only [Fin.addCases_right]
    congr 1

theorem cochainOperator_uniformGraft (Γ : BinaryGraph a 2) (Δ : BinaryGraph b 2) (r : Fin 2)
    (χ : GraftChoices (b := b) Γ r) (T : Fin a → Tensor 2 d R) (U : Fin b → Tensor 2 d R) :
    (uniformGraft Γ Δ r χ).cochainOperator (Fin.addCases T U) =
      (Γ.graft Δ r χ).cochainOperator (graftTensors (fun _ ↦ 2) (fun _ ↦ 2) T U) := by
  rw [← uniformGraftTensors_eq_addCases]
  exact cochainOperator_castGraph graftArity_two _ _

/-- Full polynomial insertion is exactly the finite sum of uniform admissible
grafts with concatenated vertex tensors; no weights or MC laws occur. -/
theorem cochainOperator_insertion (Γ : BinaryGraph a 2) (Δ : BinaryGraph b 2) (r : Fin 2)
    (T : Fin a → Tensor 2 d R) (U : Fin b → Tensor 2 d R) (f : Fin 3 → MvPolynomial (Fin d) R) :
    Γ.cochainOperator T
      (Function.update (fun j ↦ f (graftOuterBoundary (l := 1) r j)) r
        (Δ.cochainOperator U (fun j ↦ f (graftInnerBoundary (l := 1) r j)))) =
      ∑ χ : GraftChoices (b := b) Γ r,
        (uniformGraft Γ Δ r χ).cochainOperator (Fin.addCases T U) f := by
  rw [Graph.cochainOperator_graft]
  apply Finset.sum_congr rfl
  intro χ hχ
  exact congrArg (fun B ↦ B f) (cochainOperator_uniformGraft Γ Δ r χ T U).symm

theorem coordinateTensor_addCases
    (F : Fin a → Multiderivation R (MvPolynomial (Fin d) R) 2)
    (G : Fin b → Multiderivation R (MvPolynomial (Fin d) R) 2) :
    (fun v ↦ Gauge.GraphTaylorCoefficients.coordinateTensor (Fin.addCases F G v)) =
      Fin.addCases (fun v ↦ Gauge.GraphTaylorCoefficients.coordinateTensor (F v))
        (fun v ↦ Gauge.GraphTaylorCoefficients.coordinateTensor (G v)) := by
  funext v
  refine Fin.addCases (fun v ↦ ?_) (fun v ↦ ?_) v <;> simp

/-- The graft sum on genuine polynomial bivectors, valued in the existing full
arity-three cochain space. -/
def graftOperatorSum (Γ : BinaryGraph a 2) (Δ : BinaryGraph b 2) (r : Fin 2)
    (F : Fin a → Multiderivation R (MvPolynomial (Fin d) R) 2)
    (G : Fin b → Multiderivation R (MvPolynomial (Fin d) R) 2) :
    Cochain R (MvPolynomial (Fin d) R) 3 :=
  ∑ χ : GraftChoices (b := b) Γ r, operator (uniformGraft Γ Δ r χ) (Fin.addCases F G)

theorem graftOperatorSum_eq_general (Γ : BinaryGraph a 2) (Δ : BinaryGraph b 2) (r : Fin 2)
    (F : Fin a → Multiderivation R (MvPolynomial (Fin d) R) 2)
    (G : Fin b → Multiderivation R (MvPolynomial (Fin d) R) 2) :
    graftOperatorSum Γ Δ r F G = Graph.graftCochainSum Γ Δ r
      (fun v ↦ Gauge.GraphTaylorCoefficients.coordinateTensor (F v))
      (fun v ↦ Gauge.GraphTaylorCoefficients.coordinateTensor (G v)) := by
  unfold graftOperatorSum Graph.graftCochainSum
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [operator_apply, coordinateTensor_addCases, cochainOperator_uniformGraft]

theorem graftOperatorSum_left (Γ : BinaryGraph a 2) (Δ : BinaryGraph b 2)
    (F : Fin a → Multiderivation R (MvPolynomial (Fin d) R) 2)
    (G : Fin b → Multiderivation R (MvPolynomial (Fin d) R) 2) :
    cochainThreeEquiv R (MvPolynomial (Fin d) R) (graftOperatorSum Γ Δ 0 F G) =
      insertLeft (cochainTwoEquiv R (MvPolynomial (Fin d) R) (operator Γ F))
        (cochainTwoEquiv R (MvPolynomial (Fin d) R) (operator Δ G)) := by
  rw [graftOperatorSum_eq_general]
  exact Graph.graft_binary_left Γ Δ _ _

theorem graftOperatorSum_right (Γ : BinaryGraph a 2) (Δ : BinaryGraph b 2)
    (F : Fin a → Multiderivation R (MvPolynomial (Fin d) R) 2)
    (G : Fin b → Multiderivation R (MvPolynomial (Fin d) R) 2) :
    cochainThreeEquiv R (MvPolynomial (Fin d) R) (graftOperatorSum Γ Δ 1 F G) =
      insertRight (cochainTwoEquiv R (MvPolynomial (Fin d) R) (operator Γ F))
        (cochainTwoEquiv R (MvPolynomial (Fin d) R) (operator Δ G)) := by
  rw [graftOperatorSum_eq_general]
  exact Graph.graft_binary_right Γ Δ _ _

end GraftOperators
end EnvelopingIsomorphism.Deformation.UniformBinaryGraphs
