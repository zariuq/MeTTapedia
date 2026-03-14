import Mettapedia.Logic.HOL.CanonicalKripke

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

namespace ClosedTheorySet.World

/-- The canonical truth event of a closed formula: the worlds whose carrier contains it. -/
def truthEvent (φ : ClosedFormula Const) : Set (ClosedTheorySet.World Const) :=
  {W | W ∈ truthSet (Const := Const) φ}

theorem truthEvent_upper {φ : ClosedFormula Const} :
    IsUpperSet (truthEvent (Const := Const) φ) := by
  intro W V hWV hW
  exact mem_mono hWV hW

@[simp] theorem mem_truthEvent_iff {W : ClosedTheorySet.World Const}
    {φ : ClosedFormula Const} :
    W ∈ truthEvent (Const := Const) φ ↔ φ ∈ W.carrier :=
  Iff.rfl

@[simp] theorem truthEvent_top_eq_univ :
    truthEvent (Const := Const) (.top : ClosedFormula Const) = Set.univ := by
  ext W
  change (.top : ClosedFormula Const) ∈ W.carrier ↔ W ∈ Set.univ
  constructor
  · intro _
    trivial
  · intro _
    exact W.top_mem

@[simp] theorem truthEvent_and_eq_inter {φ ψ : ClosedFormula Const} :
    truthEvent (Const := Const) (.and φ ψ) =
      truthEvent (Const := Const) φ ∩ truthEvent (Const := Const) ψ := by
  ext W
  change (.and φ ψ : ClosedFormula Const) ∈ W.carrier ↔
    φ ∈ W.carrier ∧ ψ ∈ W.carrier
  exact ClosedTheorySet.World.mem_truthSet_and_iff

@[simp] theorem truthEvent_or_eq_union {φ ψ : ClosedFormula Const} :
    truthEvent (Const := Const) (.or φ ψ) =
      truthEvent (Const := Const) φ ∪ truthEvent (Const := Const) ψ := by
  ext W
  change (.or φ ψ : ClosedFormula Const) ∈ W.carrier ↔
    φ ∈ W.carrier ∨ ψ ∈ W.carrier
  exact ClosedTheorySet.World.mem_truthSet_or_iff

@[simp] theorem truthEvent_ex_eq_iUnion {σ : Ty Base} {φ : Formula Const [σ]} :
    truthEvent (Const := Const) (.ex φ : ClosedFormula Const) =
      ⋃ t : ClosedTerm Const σ, truthEvent (Const := Const) (instantiate (Base := Base) t φ) := by
  ext W
  constructor
  · intro h
    simpa [truthEvent] using
      (ClosedTheorySet.World.mem_truthSet_ex_iff
        (Const := Const) (Base := Base) (W := W) (σ := σ) (φ := φ)).mp h
  · intro h
    exact
      (ClosedTheorySet.World.mem_truthSet_ex_iff
        (Const := Const) (Base := Base) (W := W) (σ := σ) (φ := φ)).mpr
        (by simpa [truthEvent] using h)

@[simp] theorem truthEvent_all_eq_iInter {σ : Ty Base} {φ : Formula Const [σ]} :
    truthEvent (Const := Const) (.all φ : ClosedFormula Const) =
      ⋂ t : ClosedTerm Const σ, truthEvent (Const := Const) (instantiate (Base := Base) t φ) := by
  ext W
  constructor
  · intro h
    simpa [truthEvent] using
      (ClosedTheorySet.World.mem_truthSet_all_iff
        (Const := Const) (Base := Base) (W := W) (σ := σ) (φ := φ)).mp h
  · intro h
    exact
      (ClosedTheorySet.World.mem_truthSet_all_iff
        (Const := Const) (Base := Base) (W := W) (σ := σ) (φ := φ)).mpr
        (by simpa [truthEvent] using h)

theorem truthEvent_imp_subset_forces {φ ψ : ClosedFormula Const} :
    truthEvent (Const := Const) (.imp φ ψ) ⊆
      {W | ForcesImp (Const := Const) W φ ψ} := by
  intro W hW
  exact imp_mem_implies_forcesImp (Const := Const) hW

theorem truthEvent_not_subset_forces {φ : ClosedFormula Const} :
    truthEvent (Const := Const) (.not φ) ⊆
      {W | ForcesNot (Const := Const) W φ} := by
  intro W hW
  exact not_mem_implies_forcesNot (Const := Const) hW

end ClosedTheorySet.World

end Mettapedia.Logic.HOL
