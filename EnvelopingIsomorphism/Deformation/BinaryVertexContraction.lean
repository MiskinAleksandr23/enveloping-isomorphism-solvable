import EnvelopingIsomorphism.Deformation.GeneralGraphVertexSplitExtraction
import EnvelopingIsomorphism.Deformation.UniformCurvatureSplits
import EnvelopingIsomorphism.Deformation.GeneralGraphPermutations

/-! Canonical contraction of the actual one-arrow binary two-child cluster. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.BinaryVertexContraction
open KontsevichGraph.General KontsevichGraph.General.Graph
open KontsevichGraph.General.TwoVertexContraction
open UniformBinaryGraphs UniformCurvatureSplits SchoutenGraphContraction
open scoped Classical BigOperators
variable {n m : ℕ}

/-- The receiver's two slots, followed by the sender's remaining slot. -/
def canonicalLeg (a : Fin 2) : Fin 3 → Edge bivectorArity :=
  if a = 0 then ![⟨1,0⟩, ⟨1,1⟩, ⟨0,1⟩] else ![⟨0,0⟩, ⟨0,1⟩, ⟨1,1⟩]

theorem canonicalLeg_ne (a : Fin 2) (j : Fin 3) : canonicalLeg a j ≠ ⟨a,0⟩ := by
  fin_cases a <;> fin_cases j <;> decide

theorem canonicalLeg_injective (a : Fin 2) : Function.Injective (canonicalLeg a) := by
  fin_cases a <;> decide

theorem canonicalLeg_complete (a : Fin 2) (e : Edge bivectorArity) (he : e ≠ ⟨a,0⟩) :
    ∃ j, canonicalLeg a j = e := by
  rcases e with ⟨v,s⟩
  fin_cases a <;> fin_cases v <;> fin_cases s <;> first | contradiction | decide

variable {q : Fin (n + 1) → ℕ} (i : Fin (n + 1)) (hq : q i = 3)
variable (H : Graph (vertexSplitArity q bivectorArity i) m) (a : Fin 2)

/-- The unique internal arrow is in source slot zero after normalization. -/
def UniqueInternal : Prop := ∀ e : Edge bivectorArity,
  vertexSplitCollapseVertex i (H.target (vertexSplitLocalEdge q bivectorArity i e)) = Sum.inl i ↔
    e = ⟨a,0⟩

/-- The three actual exiting arrows remain distinct after contraction. -/
def ExitsDistinct : Prop := ∀ e f : Edge bivectorArity,
  e ≠ ⟨a,0⟩ → f ≠ ⟨a,0⟩ →
  vertexSplitCollapseVertex i (H.target (vertexSplitLocalEdge q bivectorArity i e)) =
    vertexSplitCollapseVertex i (H.target (vertexSplitLocalEdge q bivectorArity i f)) → e = f

variable (hi : UniqueInternal i H a) (hd : H.SplitCoarseDistinct i)
    (hx : ExitsDistinct i H a)

include hi in
theorem legsOutside : H.SplitLegsOutside i (canonicalLeg a) := by
  intro j hj
  exact canonicalLeg_ne a j ((hi _).mp hj)

include hx in
theorem legsDistinct : H.SplitLegsDistinct i (canonicalLeg a) := by
  intro j k h
  exact canonicalLeg_injective a (hx _ _ (canonicalLeg_ne a j) (canonicalLeg_ne a k) h)

include hi in
theorem legsComplete : H.SplitLegsComplete i (canonicalLeg a) := by
  intro e he
  obtain ⟨j, rfl⟩ := canonicalLeg_complete a e (fun hh ↦ he ((hi e).mpr hh))
  exact ⟨j, rfl⟩

def quotient : Graph q m := contractedGraph i hq H (canonicalLeg a)
  hd (legsOutside i H a hi) (legsDistinct i H a hx)

def choices : (quotient i hq H a hi hd hx).VertexSplitChoices i :=
  contractedChoices i hq H (canonicalLeg a) hd (legsOutside i H a hi) (legsDistinct i H a hx)

def localTemplate : Graph bivectorArity 3 := contractedTemplate i hq H (canonicalLeg a)
  hd (legsOutside i H a hi) (legsDistinct i H a hx) (legsComplete i H a hi)

theorem localTemplate_leg (j : Fin 3) :
    (localTemplate i hq H a hi hd hx).target (canonicalLeg a j) = Sum.inr j :=
  contractedTemplate_target_leg i hq H (canonicalLeg a) hd (legsOutside i H a hi)
    (legsDistinct i H a hx) (legsComplete i H a hi) j

/-- The internal edge reaches the other child, by the original graph's no-loop law. -/
theorem localTemplate_internal :
    (localTemplate i hq H a hi hd hx).target ⟨a,0⟩ = Sum.inl (Equiv.swap 0 1 a) := by
  obtain ⟨b,hb⟩ := (vertexSplitCollapse_eq_root_iff i _).mp ((hi ⟨a,0⟩).mpr rfl)
  have hba : b ≠ a := by
    intro he
    subst b
    exact H.noLoops _ _ hb.symm
  have he : b = Equiv.swap 0 1 a := by
    fin_cases a <;> fin_cases b <;> simp_all
  exact contractedTemplate_target_child i hq H (canonicalLeg a) hd (legsOutside i H a hi)
    (legsDistinct i H a hx) (legsComplete i H a hi) ⟨a,0⟩ (Equiv.swap 0 1 a) (he ▸ hb.symm)

def canonicalTemplate (a : Fin 2) : Graph bivectorArity 3 :=
  if a = 0 then bivectorForward (cyclicPermutation 0) else bivectorReverse (cyclicPermutation 0)

theorem localTemplate_eq : localTemplate i hq H a hi hd hx = canonicalTemplate a := by
  apply Graph.ext
  funext e
  by_cases he : e = ⟨a,0⟩
  · subst e
    rw [localTemplate_internal]
    fin_cases a <;> rfl
  · obtain ⟨j,rfl⟩ := canonicalLeg_complete a e he
    rw [localTemplate_leg]
    fin_cases a <;> fin_cases j <;> rfl

/-- Exact reconstruction, with the local template identified as one of the six
actual Schouten templates (the canonical cyclic index is zero). -/
theorem reconstruct :
    (quotient i hq H a hi hd hx).vertexSplit (canonicalTemplate a) i hq
      (choices i hq H a hi hd hx) = H := by
  rw [← localTemplate_eq i hq H a hi hd hx]
  exact vertexSplit_contracted i hq H (canonicalLeg a) hd (legsOutside i H a hi)
    (legsDistinct i H a hx) (legsComplete i H a hi)

end EnvelopingIsomorphism.Deformation.BinaryVertexContraction
