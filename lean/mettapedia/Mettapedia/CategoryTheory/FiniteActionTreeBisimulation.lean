import Mettapedia.CategoryTheory.FiniteActionTree

/-!
# The coloured two-sided bisimulation quotient

The relation is defined independently from the quotient. It observes the
root colour and covers both complete finite successor sets at every action.
Its greatest instance is an equivalence relation. Root colours and actual
successor images descend to that quotient, forgetting branch order and
repeated bisimilar subtrees.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.FiniteActionTree

universe a u

variable {Actions : Type a} {Colours : Type u}

def Admitted (relation : Raw Actions Colours → Raw Actions Colours → Prop) : Prop :=
  ∀ first second, relation first second → root first = root second ∧
    ∀ action, FinitePowerset.Related relation (step first action) (step second action)

def Bisimilar (first second : Raw Actions Colours) : Prop :=
  ∃ relation, Admitted relation ∧ relation first second

theorem bisimilar_of_admitted {relation : Raw Actions Colours → Raw Actions Colours → Prop}
    (admitted : Admitted relation) {first second : Raw Actions Colours}
    (held : relation first second) : Bisimilar first second := ⟨relation, admitted, held⟩

theorem bisimilar_admitted : @Admitted Actions Colours Bisimilar := by
  intro first second related
  obtain ⟨relation, admitted, held⟩ := related
  obtain ⟨colours, successors⟩ := admitted first second held
  refine ⟨colours, fun action => ?_⟩
  constructor
  · intro value member
    obtain ⟨other, otherMember, paired⟩ := (successors action).1 value member
    exact ⟨other, otherMember, relation, admitted, paired⟩
  · intro other member
    obtain ⟨value, valueMember, paired⟩ := (successors action).2 other member
    exact ⟨value, valueMember, relation, admitted, paired⟩

theorem bisimilar_root {first second : Raw Actions Colours} (held : Bisimilar first second) :
    root first = root second := (bisimilar_admitted first second held).1

theorem bisimilar_step {first second : Raw Actions Colours} (held : Bisimilar first second)
    (action : Actions) :
    FinitePowerset.Related Bisimilar (step first action) (step second action) :=
  (bisimilar_admitted first second held).2 action

theorem bisimilar_refl (tree : Raw Actions Colours) : Bisimilar tree tree := by
  refine ⟨Eq, ?_, rfl⟩
  intro first second same
  subst second
  exact ⟨rfl, fun action => FinitePowerset.related_identity (step first action)⟩

theorem bisimilar_symm {first second : Raw Actions Colours} (held : Bisimilar first second) :
    Bisimilar second first := by
  obtain ⟨relation, admitted, paired⟩ := held
  refine ⟨fun left right => relation right left, ?_, paired⟩
  intro left right swapped
  obtain ⟨colours, successors⟩ := admitted right left swapped
  exact ⟨colours.symm, fun action => ⟨(successors action).2, (successors action).1⟩⟩

theorem bisimilar_trans {first middle last : Raw Actions Colours}
    (earlier : Bisimilar first middle) (later : Bisimilar middle last) :
    Bisimilar first last := by
  obtain ⟨before, beforeAdmitted, beforePaired⟩ := earlier
  obtain ⟨after, afterAdmitted, afterPaired⟩ := later
  refine ⟨fun left right => ∃ other, before left other ∧ after other right,
    ?_, middle, beforePaired, afterPaired⟩
  rintro left right ⟨other, firstHeld, secondHeld⟩
  obtain ⟨firstColour, firstSteps⟩ := beforeAdmitted left other firstHeld
  obtain ⟨secondColour, secondSteps⟩ := afterAdmitted other right secondHeld
  exact ⟨firstColour.trans secondColour,
    fun action => FinitePowerset.related_compose (firstSteps action) (secondSteps action)⟩

def bisimulationSetoid (Actions : Type a) (Colours : Type u) : Setoid (Raw Actions Colours) where
  r := Bisimilar
  iseqv := ⟨bisimilar_refl, bisimilar_symm, bisimilar_trans⟩

def Tree (Actions : Type a) (Colours : Type u) : Type (max a u) :=
  Quotient (bisimulationSetoid Actions Colours)

def project (tree : Raw Actions Colours) : Tree Actions Colours :=
  Quotient.mk (bisimulationSetoid Actions Colours) tree

theorem project_eq_iff (first second : Raw Actions Colours) :
    project first = project second ↔ Bisimilar first second := Quotient.eq

theorem project_eq_of_bisimilar {first second : Raw Actions Colours}
    (held : Bisimilar first second) : project first = project second :=
  (project_eq_iff first second).2 held

namespace Tree

def root (tree : Tree Actions Colours) : Colours :=
  Quotient.lift FiniteActionTree.root
    (fun _ _ held => bisimilar_root held) tree

@[simp] theorem root_project (tree : Raw Actions Colours) :
    root (project tree) = FiniteActionTree.root tree := rfl

theorem step_respects {first second : Raw Actions Colours}
    (held : Bisimilar first second) (action : Actions) :
    FinitePowerset.map project (FiniteActionTree.step first action) =
      FinitePowerset.map project (FiniteActionTree.step second action) := by
  apply Finset.ext
  intro value
  rw [FinitePowerset.mem_map, FinitePowerset.mem_map]
  constructor
  · rintro ⟨next, member, rfl⟩
    obtain ⟨other, otherMember, paired⟩ := (bisimilar_step held action).1 next member
    exact ⟨other, otherMember, (project_eq_of_bisimilar paired).symm⟩
  · rintro ⟨other, member, rfl⟩
    obtain ⟨next, nextMember, paired⟩ := (bisimilar_step held action).2 other member
    exact ⟨next, nextMember, project_eq_of_bisimilar paired⟩

def step (tree : Tree Actions Colours) (action : Actions) : Finset (Tree Actions Colours) :=
  Quotient.lift (fun raw => FinitePowerset.map project (FiniteActionTree.step raw action))
    (fun _ _ held => step_respects held action) tree

@[simp] theorem step_project (tree : Raw Actions Colours) (action : Actions) :
    step (project tree) action =
      FinitePowerset.map project (FiniteActionTree.step tree action) := rfl

theorem mem_step_project (tree : Raw Actions Colours) (action : Actions)
    (next : Tree Actions Colours) :
    next ∈ step (project tree) action ↔
      ∃ slot, project (child tree action slot) = next := by
  rw [step_project, FinitePowerset.mem_map]
  constructor
  · rintro ⟨raw, member, same⟩
    obtain ⟨slot, rfl⟩ := (mem_step tree action raw).1 member
    exact ⟨slot, same⟩
  · rintro ⟨slot, same⟩
    exact ⟨child tree action slot, child_mem_step tree action slot, same⟩

end Tree

end Mettapedia.CategoryTheory.FiniteActionTree
