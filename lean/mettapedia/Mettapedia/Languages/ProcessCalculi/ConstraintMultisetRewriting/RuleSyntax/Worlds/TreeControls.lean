import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Tree
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Examples

/-!
# What is inherited in a tree of worlds, and what is not: controls on first-order atoms

Trees with a root and one child (`Worlds.Tree`), at the one frame of first-order atoms
(`RuleSyntax.Examples`).

* `gained_below`: the root holds the row `x` and knows nothing; the child knows `x = 5`. What the
  root sees is `Examples.openRequest`, what the child sees is `Examples.boundRequest`. **The none query
  of `9` is refused at the root and admitted at the child**: a none query is not reflected upward.
* `lost_below`: the child holds the row `9`. **The none query of `9` is admitted at the root and refused
  at the child**: a none query is not inherited.
* `may_not_inherited`: the row `x` may be read as `9` at the root, and not at the child that knows
  `x = 5`. `must_inherited`: it must be read as a term at both, an instance of `Tree.mustBarb_below`.
* `dead_child_live_parent`: a child whose own store has no solution, under a root whose knowledge is
  solvable: a contradiction does not reach upward. `dead_root_dead_child`: it does hold below, an
  instance of `Tree.dead_below`.
* `none_inherited`: a child that adds neither knowledge nor a row knows what its parent knows and
  inherits the none query of `9`: instances of `Tree.known_child` and `Tree.none_below_of_no_new_row`.
* `gathering_not_stable`: the rows at the root and below it are none before the child makes its row,
  and one after: a count over what the children have answered holds only while no child makes a row.
-/

set_option autoImplicit false

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Examples
  (Tm X E x c demo everywhere openRequest boundRequest noNineFiring noNine_fresh
    noNine_admitted_when_bound noNine_refused_when_open)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls (atoms)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence
  (Pattern MayBarb MustBarb)
open Mettapedia.Logic.LP

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Controls

open Interface (Frames)

/-! ## A child that knows more -/

/-- A root that holds the row `x` and knows nothing; a child that knows `x = 5`. -/
def knowingChild : Tree Tm ℕ Bool where
  frame := PUnit.unit
  chain n := cond n [false, true] [false]
  stores n := cond n [(x, c 5)] []
  present := {0}
  label _ := x
  place _ := false

/-- The child is below the root. -/
theorem knowingChild_below : knowingChild.Below false true := by
  intro a member
  have isRoot : a = false := List.mem_singleton.mp member
  subst isRoot
  exact List.mem_cons_self

/-- The root and the child both see the row. -/
theorem knowingChild_visible (n : Bool) : knowingChild.visible n = {0} := by
  ext o
  rw [Tree.mem_visible]
  constructor
  · exact fun inside => inside.1
  · intro inside
    refine ⟨inside, ?_⟩
    cases n <;> exact List.mem_cons_self

/-- What the root sees: the row `x`, nothing known. -/
theorem root_view : knowingChild.view false = openRequest := by
  show (⟨PUnit.unit, [], knowingChild.visible false, fun _ => x⟩ : State Tm ℕ) = openRequest
  rw [knowingChild_visible]
  rfl

/-- What the child sees: the row `x`, and `x = 5`. -/
theorem child_view : knowingChild.view true = boundRequest := by
  show (⟨PUnit.unit, [(x, c 5)], knowingChild.visible true, fun _ => x⟩ : State Tm ℕ) = boundRequest
  rw [knowingChild_visible]
  rfl

/-- **A none query is not reflected upward**: the child is below the root; they see the states named; the
none queries of `9` is refused at the root and admitted at the child. -/
theorem gained_below :
    knowingChild.Below false true ∧ knowingChild.view false = openRequest ∧
      knowingChild.view true = boundRequest ∧
      ¬ (step X ℕ E demo).Admits (s := openRequest) noNineFiring ∧
      (step X ℕ E demo).Admits (s := boundRequest) noNineFiring :=
  ⟨knowingChild_below, root_view, child_view, noNine_refused_when_open, noNine_admitted_when_bound⟩

/-- The pattern `9`. -/
def nine : Pattern Tm := ⟨PUnit.unit, c 9⟩

/-- Any term: the pattern that is one unknown. -/
def anyTerm : Pattern Tm := ⟨PUnit.unit, x⟩

/-- **A may-barb is not inherited**: at the root the row `x` may be read as `9`; at the child, which
knows `x = 5`, it may not. -/
theorem may_not_inherited : MayBarb X nine openRequest ∧ ¬ MayBarb X nine boundRequest := by
  refine ⟨⟨0, Finset.mem_singleton_self 0, PUnit.unit, everywhere 9, Subst.id atoms,
    fun e member => absurd member List.not_mem_nil, rfl⟩, ?_⟩
  rintro ⟨o, -, b, σ, h, known, equated⟩
  have bound : σ 0 = c 5 := known (x, c 5) List.mem_cons_self
  have read : σ 0 = c 9 := equated
  exact absurd (Term.const.inj (bound.symm.trans read)) (by decide)

/-- **A must-barb is inherited**: the row is a term at the root, hence at the child. -/
theorem must_inherited :
    MustBarb X anyTerm (knowingChild.view false) ∧ MustBarb X anyTerm (knowingChild.view true) := by
  have atRoot : MustBarb X anyTerm (knowingChild.view false) := by
    rw [root_view]
    exact ⟨0, Finset.mem_singleton_self 0, fun b σ _ => ⟨σ, rfl⟩⟩
  exact ⟨atRoot, Tree.mustBarb_below X knowingChild_below atRoot⟩

/-! ## A child whose knowledge has no solution -/

/-- A root that knows nothing, and a child whose own store equates `1` and `2`. -/
def deadChild : Tree Tm ℕ Bool where
  frame := PUnit.unit
  chain n := cond n [false, true] [false]
  stores n := cond n [(c 1, c 2)] []
  present := ∅
  label _ := c 0
  place _ := false

/-- **A contradiction does not reach upward**: the child's knowledge has no solution, the root's
has. -/
theorem dead_child_live_parent :
    ¬ X.Solvable (a := PUnit.unit) (deadChild.known true) ∧
      X.Solvable (a := PUnit.unit) (deadChild.known false) := by
  refine ⟨?_, ⟨PUnit.unit, Subst.id atoms, fun e member => absurd member List.not_mem_nil⟩⟩
  rintro ⟨_, σ, solved⟩
  have same : (c 1 : Term atoms) = c 2 := solved (c 1, c 2) List.mem_cons_self
  exact absurd (Term.const.inj same) (by decide)

/-- A root whose own store equates `1` and `2`, and a child that adds nothing. -/
def deadRoot : Tree Tm ℕ Bool where
  frame := PUnit.unit
  chain n := cond n [false, true] [false]
  stores n := cond n [] [(c 1, c 2)]
  present := ∅
  label _ := c 0
  place _ := false

/-- **A contradiction at the root holds below it**: an instance of `Tree.dead_below`. -/
theorem dead_root_dead_child : ¬ X.Solvable (a := PUnit.unit) (deadRoot.known true) := by
  refine Tree.dead_below X (t := deadRoot) (n := false) (m := true) ?_ ?_
  · intro a member
    have isRoot : a = false := List.mem_singleton.mp member
    subst isRoot
    exact List.mem_cons_self
  · rintro ⟨_, σ, solved⟩
    have same : (c 1 : Term atoms) = c 2 := solved (c 1, c 2) List.mem_cons_self
    exact absurd (Term.const.inj same) (by decide)

/-! ## A child that adds nothing -/

/-- A root that holds the row `x` and knows `x = 5`; a child with no knowledge and no row of its
own. -/
def idleChild : Tree Tm ℕ Bool where
  frame := PUnit.unit
  chain n := cond n [false, true] [false]
  stores n := cond n [] [(x, c 5)]
  present := {0}
  label _ := x
  place _ := false

theorem idleChild_below : idleChild.Below false true := by
  intro a member
  have isRoot : a = false := List.mem_singleton.mp member
  subst isRoot
  exact List.mem_cons_self

theorem idleChild_visible (n : Bool) : idleChild.visible n = {0} := by
  ext o
  rw [Tree.mem_visible]
  constructor
  · exact fun inside => inside.1
  · intro inside
    refine ⟨inside, ?_⟩
    cases n <;> exact List.mem_cons_self

/-- **A child that adds nothing knows what its parent knows, and inherits its none checks**: instances of
`Tree.known_child` and of `Tree.none_below_of_no_new_row`, with the none query of `9`. -/
theorem none_inherited :
    idleChild.known true = idleChild.known false ∧
      X.Entails (a := PUnit.unit) (idleChild.known true)
        (fun b σ => checkHolds X (a := PUnit.unit) (b := b) σ idleChild.label (idleChild.visible true)
          (.predicate .none (c 9))) := by
  have atRoot : X.Entails (a := PUnit.unit) (idleChild.known false)
      (fun b σ => checkHolds X (a := PUnit.unit) (b := b) σ idleChild.label (idleChild.visible false)
        (.predicate .none (c 9))) := by
    intro b σ solved
    have known : X.Models (a := PUnit.unit) (b := b) σ [(x, c 5)] := solved
    have bound : σ 0 = c 5 := known (x, c 5) List.mem_cons_self
    intro o _ equated
    have nine : (c 9 : Term atoms) = σ 0 := equated
    rw [bound] at nine
    exact absurd (Term.const.inj nine) (by decide)
  exact ⟨Tree.known_child rfl rfl,
    Tree.none_below_of_no_new_row X idleChild_below
      ((idleChild_visible true).trans (idleChild_visible false).symm) (c 9) atRoot⟩

/-! ## A child that holds a row -/

/-- A root with no row; a child that holds the row `9`, when it has made it. -/
def holdingChild (made : Bool) : Tree Tm ℕ Bool where
  frame := PUnit.unit
  chain n := cond n [false, true] [false]
  stores _ := []
  present := cond made {1} ∅
  label _ := c 9
  place _ := true

/-- The root sees no row. -/
theorem holdingChild_root (made : Bool) : (holdingChild made).visible false = ∅ := by
  ext o
  rw [Tree.mem_visible]
  constructor
  · rintro ⟨-, above⟩
    have wrong : true = false := List.mem_singleton.mp above
    exact absurd wrong (by decide)
  · intro inside
    exact absurd inside (Finset.notMem_empty o)

/-- **At the root the none query of `9` is admitted.** -/
theorem none_at_root :
    (step X ℕ E demo).Admits (s := (holdingChild true).view false) noNineFiring := by
  show noNineFiring.Admits X ((holdingChild true).view false)
  refine ⟨⟨noNine_fresh _, List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [noNineFiring, Selection.commit]
  · exact ⟨PUnit.unit, Subst.id atoms, fun e inside => absurd inside List.not_mem_nil⟩
  · intro b σ _
    refine ⟨fun check inside => ?_, fun q inside => absurd inside List.not_mem_nil⟩
    have isNone : check = Check.predicate .none (c 9) := List.mem_singleton.mp inside
    subst isNone
    intro o present
    exact absurd (Eq.mp (congrArg (fun s : Finset ℕ => o ∈ s) (holdingChild_root true)) present)
      (Finset.notMem_empty o)

/-- **At the child, which holds the row `9`, it is refused.** -/
theorem none_refused_at_child :
    ¬ (step X ℕ E demo).Admits (s := (holdingChild true).view true) noNineFiring := by
  intro admitted
  obtain ⟨-, -, -, -, checks, -⟩ := (admits_iff noNineFiring).mp admitted
  have solved : X.Models (a := PUnit.unit) (b := PUnit.unit) (Subst.id atoms)
      (noNineFiring.information X ((holdingChild true).view true)) :=
    fun e inside => absurd inside List.not_mem_nil
  have holds := checks (.predicate .none (c 9)) (List.mem_singleton_self _) PUnit.unit _ solved
  exact holds 1 (Tree.mem_visible.mpr
    ⟨Finset.mem_singleton_self 1, List.mem_cons_of_mem _ List.mem_cons_self⟩) rfl

/-- **A none query is not inherited**: admitted at the root, refused at the child that holds the row. -/
theorem lost_below :
    (step X ℕ E demo).Admits (s := (holdingChild true).view false) noNineFiring ∧
      ¬ (step X ℕ E demo).Admits (s := (holdingChild true).view true) noNineFiring :=
  ⟨none_at_root, none_refused_at_child⟩

/-- **What a collection gathers is not stable while a child makes rows**: the rows at the root and
below it are none before the child makes its row, and one after. -/
theorem gathering_not_stable :
    ((holdingChild false).gathered false).card = 0 ∧ ((holdingChild true).gathered false).card = 1 := by
  have before : (holdingChild false).gathered false = ∅ := by
    ext o
    rw [Tree.mem_gathered]
    constructor
    · rintro ⟨inside, -⟩
      exact inside
    · intro inside
      exact absurd inside (Finset.notMem_empty o)
  have after : (holdingChild true).gathered false = {1} := by
    ext o
    rw [Tree.mem_gathered]
    constructor
    · rintro ⟨inside, -⟩
      exact inside
    · intro inside
      exact ⟨inside, List.mem_cons_self⟩
  rw [before, after]
  exact ⟨Finset.card_empty, Finset.card_singleton 1⟩

#print axioms gained_below
#print axioms may_not_inherited
#print axioms must_inherited
#print axioms dead_child_live_parent
#print axioms dead_root_dead_child
#print axioms none_inherited
#print axioms none_at_root
#print axioms none_refused_at_child
#print axioms lost_below
#print axioms gathering_not_stable

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Controls
