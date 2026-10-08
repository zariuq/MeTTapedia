import Mettapedia.CategoryTheory.FiniteActionTreeBisimulation

/-!
# Coiteration and uniqueness for unordered finite action trees

Every actual labelwise finite coalgebra and supplied colour map produce a
whole tree. The complete successor equation follows from the independent
finite enumeration. A colour-preserving coalgebra map is unique: its raw
representatives and the constructed raw coiterations form a two-sided
bisimulation. No branch order is required of that map or its enumeration.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.FiniteActionTree.Tree

universe a u v w

variable {Actions : Type a} {Colours : Type u}

def coiterate {States : Type v} (successors : States → Actions → Finset States)
    (colour : States → Colours) (state : States) : Tree Actions Colours :=
  project (coiterateRaw successors colour state)

@[simp] theorem root_coiterate {States : Type v}
    (successors : States → Actions → Finset States) (colour : States → Colours)
    (state : States) : root (coiterate successors colour state) = colour state :=
  root_coiterateRaw successors colour state

theorem step_coiterate {States : Type v}
    (successors : States → Actions → Finset States) (colour : States → Colours)
    (state : States) (action : Actions) :
    step (coiterate successors colour state) action =
      FinitePowerset.map (coiterate successors colour) (successors state action) := by
  rw [coiterate, step_project, step_coiterateRaw, FinitePowerset.map_compose]
  rfl

/-- Both successor directions are obtained from the actual candidate square. -/
theorem coiterate_unique {States : Type v}
    (successors : States → Actions → Finset States) (colour : States → Colours)
    (mapping : States → Tree Actions Colours)
    (roots : ∀ state, root (mapping state) = colour state)
    (squares : ∀ state action,
      step (mapping state) action = FinitePowerset.map mapping (successors state action)) :
    ∀ state, mapping state = coiterate successors colour state := by
  let relation : Raw Actions Colours → Raw Actions Colours → Prop :=
    fun first second => ∃ state,
      project first = mapping state ∧ second = coiterateRaw successors colour state
  have admitted : Admitted relation := by
    rintro first _ ⟨state, same, rfl⟩
    refine ⟨?_, fun action => ?_⟩
    · calc
        FiniteActionTree.root first = root (project first) := rfl
        _ = root (mapping state) := congrArg root same
        _ = colour state := roots state
        _ = FiniteActionTree.root (coiterateRaw successors colour state) :=
          (root_coiterateRaw successors colour state).symm
    · constructor
      · intro next member
        have quotientMember : project next ∈ step (mapping state) action := by
          rw [← same, step_project, FinitePowerset.mem_map]
          exact ⟨next, member, rfl⟩
        rw [squares, FinitePowerset.mem_map] at quotientMember
        obtain ⟨nextState, stateMember, sameNext⟩ := quotientMember
        refine ⟨coiterateRaw successors colour nextState, ?_, nextState, sameNext.symm, rfl⟩
        rw [step_coiterateRaw, FinitePowerset.mem_map]
        exact ⟨nextState, stateMember, rfl⟩
      · intro next member
        rw [step_coiterateRaw, FinitePowerset.mem_map] at member
        obtain ⟨nextState, stateMember, rfl⟩ := member
        have quotientMember : mapping nextState ∈ step (project first) action := by
          rw [same, squares, FinitePowerset.mem_map]
          exact ⟨nextState, stateMember, rfl⟩
        rw [step_project, FinitePowerset.mem_map] at quotientMember
        obtain ⟨next, nextMember, sameNext⟩ := quotientMember
        exact ⟨next, nextMember, nextState, sameNext, rfl⟩
  intro state
  obtain ⟨raw, representative⟩ := Quotient.exists_rep (mapping state)
  have paired : Bisimilar raw (coiterateRaw successors colour state) :=
    bisimilar_of_admitted admitted ⟨state, representative, rfl⟩
  exact representative.symm.trans (project_eq_of_bisimilar paired)

/-- Coiteration is natural in actual coalgebra maps, even when they identify states. -/
theorem coiterate_natural {First : Type v} {Second : Type w}
    (before : First → Actions → Finset First) (after : Second → Actions → Finset Second)
    (mapping : First → Second)
    (squares : ∀ state action,
      FinitePowerset.map mapping (before state action) = after (mapping state) action)
    (colour : Second → Colours) (state : First) :
    coiterate before (colour ∘ mapping) state = coiterate after colour (mapping state) := by
  apply Eq.symm
  apply coiterate_unique before (colour ∘ mapping)
    (fun value => coiterate after colour (mapping value))
    (fun _ => root_coiterate after colour _)
  intro value action
  rw [step_coiterate, ← squares, FinitePowerset.map_compose]
  rfl

def map {Other : Type v} (mapping : Colours → Other) (tree : Tree Actions Colours) :
    Tree Actions Other := coiterate step (mapping ∘ root) tree

@[simp] theorem root_map {Other : Type v} (mapping : Colours → Other)
    (tree : Tree Actions Colours) : root (map mapping tree) = mapping (root tree) :=
  root_coiterate step (mapping ∘ root) tree

theorem step_map {Other : Type v} (mapping : Colours → Other)
    (tree : Tree Actions Colours) (action : Actions) :
    step (map mapping tree) action = FinitePowerset.map (map mapping) (step tree action) :=
  step_coiterate step (mapping ∘ root) tree action

@[simp] theorem map_id (tree : Tree Actions Colours) : map id tree = tree := by
  apply Eq.symm
  exact coiterate_unique step root id (fun _ => rfl)
    (fun value _ => (FinitePowerset.map_identity (step value _)).symm) tree

theorem map_comp {Other : Type v} {Last : Type w}
    (before : Colours → Other) (after : Other → Last) (tree : Tree Actions Colours) :
    map after (map before tree) = map (after ∘ before) tree := by
  apply coiterate_unique step ((after ∘ before) ∘ root)
    (fun value => map after (map before value))
  · intro value
    rw [root_map, root_map]
    rfl
  · intro value action
    rw [step_map, step_map, FinitePowerset.map_compose]
    rfl

theorem map_coiterate {States : Type v} {Other : Type w}
    (successors : States → Actions → Finset States) (colour : States → Colours)
    (mapping : Colours → Other) (state : States) :
    map mapping (coiterate successors colour state) =
      coiterate successors (mapping ∘ colour) state := by
  apply coiterate_unique successors (mapping ∘ colour)
    (fun value => map mapping (coiterate successors colour value))
  · intro value
    rw [root_map, root_coiterate]
    rfl
  · intro value action
    rw [step_map, step_coiterate, FinitePowerset.map_compose]
    rfl

def duplicate (tree : Tree Actions Colours) : Tree Actions (Tree Actions Colours) :=
  coiterate step id tree

@[simp] theorem root_duplicate (tree : Tree Actions Colours) : root (duplicate tree) = tree :=
  root_coiterate step id tree

theorem step_duplicate (tree : Tree Actions Colours) (action : Actions) :
    step (duplicate tree) action = FinitePowerset.map duplicate (step tree action) :=
  step_coiterate step id tree action

end Mettapedia.CategoryTheory.FiniteActionTree.Tree
