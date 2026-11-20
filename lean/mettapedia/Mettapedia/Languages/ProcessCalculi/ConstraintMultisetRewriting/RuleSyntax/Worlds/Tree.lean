import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Systems
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Located

/-!
# A candidate state: worlds as a tree, with knowledge and rows inherited downward

A **candidate** for a state of the step in which worlds are nested: one frame; for each world the
chain of the worlds above it, itself last; a store of equations and rows at each world.

* `Tree`, `Tree.known`, `Tree.visible`, `Tree.view`: **a world knows what the worlds above it know and
  what it knows itself, and sees their rows and its own.** What a world sees is a state of the present
  step. `Tree.Below t n m`: every world above `n` is above `m`.
* **The candidate with a store at each location is the tree of depth one**
  (`ofLocated`, `view_ofLocated`): the shared space is the root, with no knowledge; each location is a
  child; what a location sees is what the child sees. With the one-location theorem of
  `Hosting.Alternatives.Located`, the present step is the tree with one child and an empty root.

## What is inherited

* `known_mono`, `visible_mono`: knowledge and rows grow downward.
* `entails_below`: **what is known at a world is known at every world below it**: an ask answered at
  `n` is answered at `m`.
* `dead_below`: a world below a world whose knowledge has no solution has none either: a contradiction
  holds in its subtree. It does not reach upward: `Worlds.Controls.dead_child_live_parent`.
* `mustBarb_below`: a must-barb at a world is a must-barb at every world below it.
* `known_child`: a new child with no knowledge of its own knows exactly what its parent knows.

## What is not

A none query at a world is not inherited, and it is not reflected; a may-barb is not inherited; the
number of rows at a world and below it (`Tree.gathered`, what a collection at the world gathers) is
not stable while a child still makes rows (`Worlds.Controls`). One case of the none query is inherited:

* `none_below_of_no_new_row`: **a none query known at a world is known at a world below it that sees
  no further row.** Knowledge added below only removes solutions, and a none query holds at every
  solution; what can end it is a row.
-/

set_option autoImplicit false

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence
  (Pattern MustBarb)

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds

open Interface (Frames)
open Hosting.Alternatives.Located (LState)

universe uO uT uH uOcc uN uL

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

/-- **A tree of worlds (a candidate state)**: one frame; for each world the chain of the worlds above
it, itself last; a store at each world; the present rows with their labels and the world each is
at. -/
structure Tree (Tm : Obj → Type uT) (O : Type uOcc) (N : Type uN) where
  frame : Obj
  chain : N → List N
  stores : N → EquationStore (Tm frame)
  present : Finset O
  label : O → Tm frame
  place : O → N

namespace Tree

variable {O : Type uOcc} {N : Type uN}

/-- `m` is below `n`: every world above `n` is above `m`. -/
def Below (t : Tree Tm O N) (n m : N) : Prop := ∀ a ∈ t.chain n, a ∈ t.chain m

/-- **What a world knows**: the stores of the worlds above it, and its own. -/
def known (t : Tree Tm O N) (n : N) : EquationStore (Tm t.frame) := (t.chain n).flatMap t.stores

theorem known_mono {t : Tree Tm O N} {n m : N} (below : t.Below n m) :
    ∀ e ∈ t.known n, e ∈ t.known m := by
  intro e member
  obtain ⟨a, inChain, inStore⟩ := List.mem_flatMap.mp member
  exact List.mem_flatMap.mpr ⟨a, below a inChain, inStore⟩

/-- **What is known at a world is known at every world below it.** -/
theorem entails_below (X : Frames Tm Hom) {t : Tree Tm O N} {n m : N} (below : t.Below n m)
    {observation : (b : Obj) → Hom t.frame b → Prop} (asked : X.Entails (t.known n) observation) :
    X.Entails (t.known m) observation :=
  Frames.Entails.of_subset (known_mono below) asked

/-- **A world below a world whose knowledge has no solution has none either.** -/
theorem dead_below (X : Frames Tm Hom) {t : Tree Tm O N} {n m : N} (below : t.Below n m)
    (dead : ¬ X.Solvable (t.known n)) : ¬ X.Solvable (t.known m) :=
  fun alive => dead (Frames.solvable_of_subset (known_mono below) alive)

/-- **A new child with no knowledge of its own knows exactly what its parent knows.** -/
theorem known_child {t : Tree Tm O N} {n c : N} (chainEq : t.chain c = t.chain n ++ [c])
    (storeEq : t.stores c = []) : t.known c = t.known n := by
  unfold known
  rw [chainEq, List.flatMap_append]
  show (t.chain n).flatMap t.stores ++ (t.stores c ++ []) = _
  rw [storeEq]
  exact List.append_nil _

/-- **The rows a world sees**: the rows at the worlds above it, and its own. -/
noncomputable def visible (t : Tree Tm O N) (n : N) : Finset O := by
  classical
  exact t.present.filter fun o => t.place o ∈ t.chain n

theorem mem_visible {t : Tree Tm O N} {n : N} {o : O} :
    o ∈ t.visible n ↔ o ∈ t.present ∧ t.place o ∈ t.chain n := by
  classical
  unfold visible
  convert Finset.mem_filter

/-- **The view of a world**: the state of the present step that the world sees. -/
noncomputable def view (t : Tree Tm O N) (n : N) : State Tm O :=
  ⟨t.frame, t.known n, t.visible n, t.label⟩

/-- **The rows at a world and below it**: what a collection at the world gathers. -/
noncomputable def gathered (t : Tree Tm O N) (n : N) : Finset O := by
  classical
  exact t.present.filter fun o => n ∈ t.chain (t.place o)

theorem mem_gathered {t : Tree Tm O N} {n : N} {o : O} :
    o ∈ t.gathered n ↔ o ∈ t.present ∧ n ∈ t.chain (t.place o) := by
  classical
  unfold gathered
  convert Finset.mem_filter

theorem visible_mono {t : Tree Tm O N} {n m : N} (below : t.Below n m) : t.visible n ⊆ t.visible m := by
  intro o member
  obtain ⟨present, placed⟩ := mem_visible.mp member
  exact mem_visible.mpr ⟨present, below _ placed⟩

/-- **A must-barb at a world is a must-barb at every world below it.** -/
theorem mustBarb_below (X : Frames Tm Hom) {t : Tree Tm O N} {n m : N} (below : t.Below n m)
    {p : Pattern Tm} (must : MustBarb X p (t.view n)) : MustBarb X p (t.view m) := by
  obtain ⟨o, present, every⟩ := must
  exact ⟨o, visible_mono below present, fun b σ solved =>
    every b σ (Frames.models_of_subset (known_mono below) solved)⟩

/-- **A none query known at a world is known at a world below it that sees no further row.** -/
theorem none_below_of_no_new_row (X : Frames Tm Hom) {t : Tree Tm O N} {n m : N}
    (below : t.Below n m) (sameRows : t.visible m = t.visible n) (pattern : Tm t.frame)
    (asked : X.Entails (t.known n)
      (fun _ σ => checkHolds X σ t.label (t.visible n) (.predicate .none pattern))) :
    X.Entails (t.known m) (fun _ σ => checkHolds X σ t.label (t.visible m) (.predicate .none pattern)) := by
  rw [sameRows]
  exact entails_below X below asked

end Tree

/-! ## The candidate with a store at each location is the tree of depth one -/

section DepthOne

variable {O : Type uOcc} {L : Type uL}

/-- **A located state as a tree of depth one**: the shared space is the root, with no knowledge; each
location is a child of the root. -/
def ofLocated (s : LState Tm O L) : Tree Tm O (Option L) where
  frame := s.frame
  chain := fun n =>
    match n with
    | none => [none]
    | some ℓ => [none, some ℓ]
  stores := fun n =>
    match n with
    | none => []
    | some ℓ => s.stores ℓ
  present := s.present
  label := s.label
  place := s.place

/-- Every location is below the shared space. -/
theorem ofLocated_below (s : LState Tm O L) (ℓ : L) : (ofLocated s).Below none (some ℓ) := by
  intro a member
  have isRoot : a = none := List.mem_singleton.mp member
  subst isRoot
  exact List.mem_cons_self

variable [DecidableEq L]

/-- **What a location sees is what the child sees.** -/
theorem view_ofLocated (s : LState Tm O L) (ℓ : L) : (ofLocated s).view (some ℓ) = s.view ℓ := by
  have known : (ofLocated s).known (some ℓ) = s.stores ℓ := by
    show s.stores ℓ ++ [] = s.stores ℓ
    exact List.append_nil _
  have visible : (ofLocated s).visible (some ℓ) = s.visible ℓ := by
    ext o
    rw [Tree.mem_visible]
    constructor
    · rintro ⟨present, placed⟩
      refine Finset.mem_filter.mpr ⟨present, ?_⟩
      rcases List.mem_cons.mp placed with root | rest
      · exact Or.inr root
      · exact Or.inl (List.mem_singleton.mp rest)
    · intro member
      obtain ⟨present, placed⟩ := Finset.mem_filter.mp member
      refine ⟨present, ?_⟩
      rcases placed with here | root
      · exact List.mem_cons_of_mem _ (List.mem_singleton.mpr here)
      · exact List.mem_cons.mpr (Or.inl root)
  show (⟨s.frame, (ofLocated s).known (some ℓ), (ofLocated s).visible (some ℓ), s.label⟩ :
    State Tm O) = ⟨s.frame, s.stores ℓ, s.visible ℓ, s.label⟩
  rw [known, visible]

end DepthOne

#print axioms Tree.known_mono
#print axioms Tree.entails_below
#print axioms Tree.dead_below
#print axioms Tree.known_child
#print axioms Tree.visible_mono
#print axioms Tree.mustBarb_below
#print axioms Tree.none_below_of_no_new_row
#print axioms ofLocated_below
#print axioms view_ofLocated

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds
