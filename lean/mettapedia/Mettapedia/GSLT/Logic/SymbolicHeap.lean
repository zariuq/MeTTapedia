import Mettapedia.GSLT.Logic.WeakestPrecondition

/-!
# Symbolic heaps: frame inference, framed facts and entailment

A proof about a program over local actions keeps one hypothesis `h : T σ`
about the current state, where `T` is a tree of separating conjunctions.  Three
judgments, each proved once over any separation algebra, are what such a proof
needs from `T`:

* `Splits T P F`: the resource `T` holds a footprint `P` beside a frame `F`.
  The frame rule (`wp_call_framed`) consumes it: a call that needs `P` runs
  with `F` untouched beside it.  This is frame inference.
* `Ensures T O`: every resource satisfying `T` satisfies an observation `O`.
  When `O` is `Persistent` (it survives adding a separate resource), it is
  found in any one conjunct of `T`.  Pure facts, the contents a load reads and
  pointer validity are persistent observations.
* `Entails T G`: the final entailment, by splitting each conjunct of `G` off
  `T`.

An iterated conjunction `bigSep (D.map f)` over a list, such as the
representation of a store of modules, is searched through its members:
`Splits.bigSep_mem` splits the member `f i` off, given `i ∈ D`, and
`Ensures.bigSep_mem` reads an observation off it.  Membership side conditions
go to `sep_member`, which also steps through the members already erased.

The judgments are one-field structures rather than definitions, so that
unification never looks inside them: a rule applies to a judgment only by its
stated shape.

The tactics search these judgments structurally, through the conjunction tree,
by applying the lemmas of this file; they never assert anything themselves, so
whatever they prove the kernel checks against these lemmas.  Atom-level rules
are extension points (`sep_split_atom`, `sep_split_weaken`, `sep_ensures_atom`,
`sep_persistent`, `sep_entails_atom`), extended with `macro_rules`.  What an
extension produces is checked by the kernel like any other proof, so an
extension can make the search succeed more often, never prove something
false.

* `sep_split`: solves `Splits T P ?F`, choosing the frame.
* `sep_ensures`: solves `Ensures T O`.
* `sep_entails`: solves `Entails T G`; `sep_exact h` closes `G σ` from
  `h : T σ`.
* `sep_norm`: pulls pure facts, existentials and disjunctions out of
  separating conjunctions, so that `rcases` can take them apart.
* `sep_call spec`: in a goal `c.wp act Q σ`, calls `c` through its
  specification `spec`, finding the precondition in a hypothesis about `σ`
  and framing the rest.

## Examples

* **Positive.**  A footprint is found anywhere in a conjunction, and the frame
  is the rest (`Controls.split_middle`); an entailment holds up to the order
  and grouping of conjuncts (`Controls.entails_reordered`).
* **Negative.**  A footprint absent from the resource is not split off: in
  bags, `{1}` does not split off `{2} ∗ {3}`, whatever the frame
  (`Controls.absent_footprint_not_split`), and the search reports failure on
  it rather than returning a split (the `#guard_msgs` test below it).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Logic.AbstractSeparationLogic

open Mettapedia.GSLT.SeparationAlgebra
open scoped Mettapedia.GSLT.SeparationAlgebra

universe u v s

/-! ## Observations and entailment -/

section Observations

variable {S : Type s}

/-- **Every resource satisfying `T` satisfies the observation `O`.** -/
structure Ensures (T O : S → Prop) : Prop where
  intro ::
  elim : ∀ σ, T σ → O σ

/-- **Every resource satisfying `T` satisfies `G`.** -/
structure Entails (T G : S → Prop) : Prop where
  intro ::
  elim : ∀ σ, T σ → G σ

theorem Ensures.apply {T O : S → Prop} (ensures : Ensures T O) {σ : S} (holds : T σ) : O σ :=
  ensures.elim σ holds

theorem Entails.apply {T G : S → Prop} (entails : Entails T G) {σ : S} (holds : T σ) : G σ :=
  entails.elim σ holds

theorem Entails.refl (T : S → Prop) : Entails T T :=
  ⟨fun _ holds => holds⟩

theorem Entails.of_le {T G : S → Prop} (le : T ≤ G) : Entails T G :=
  ⟨le⟩

/-- The pure part of a resource with a pure fact. -/
theorem Ensures.pure (φ : Prop) (P : S → Prop) : Ensures (fun σ => φ ∧ P σ) (fun _ => φ) :=
  ⟨fun _ holds => holds.1⟩

/-- An observation of the spatial part of a resource with a pure fact. -/
theorem Ensures.and {φ : Prop} {P O : S → Prop} (inner : Ensures P O) :
    Ensures (fun σ => φ ∧ P σ) O :=
  ⟨fun σ holds => inner.elim σ holds.2⟩

/-- An observation of every witness is an observation of the existential. -/
theorem Ensures.exists {ι : Sort*} {P : ι → S → Prop} {O : S → Prop}
    (inner : ∀ i, Ensures (P i) O) : Ensures (fun σ => ∃ i, P i σ) O := by
  refine ⟨?_⟩
  rintro σ ⟨i, holds⟩
  exact (inner i).elim σ holds

end Observations

section Symbolic

variable {S : Type s} [Zero S] [Add S] [SepAlgebra S]

/-! ## Normal forms -/

theorem sepConj_or_left (P Q R : S → Prop) :
    ((fun σ => P σ ∨ Q σ) ∗ R) = fun σ => (P ∗ R) σ ∨ (Q ∗ R) σ := by
  rw [sepConj_comm, sepConj_or_right]
  simp only [sepConj_comm R]

theorem sepConj_false_left (R : S → Prop) : ((fun _ => False) ∗ R) = fun _ => False := by
  funext σ
  apply propext
  constructor
  · rintro ⟨-, -, -, -, impossible, -⟩
    exact impossible
  · exact False.elim

theorem sepConj_false_right (P : S → Prop) : (P ∗ fun _ => False) = fun _ => False := by
  rw [sepConj_comm, sepConj_false_left]

/-! ## Splitting off a footprint -/

/-- **`T` holds the footprint `P` beside the frame `F`.** -/
structure Splits (T P F : S → Prop) : Prop where
  intro ::
  elim : ∀ σ, T σ → (P ∗ F) σ

theorem Splits.apply {T P F : S → Prop} (split : Splits T P F) {σ : S} (holds : T σ) :
    (P ∗ F) σ :=
  split.elim σ holds

/-- A resource is its own footprint, with nothing beside it. -/
theorem Splits.self (P : S → Prop) : Splits P P emp := by
  refine ⟨fun σ holds => ?_⟩
  rw [sepConj_emp]
  exact holds

/-- The left conjunct is a footprint; the right one is its frame. -/
theorem Splits.here (P B : S → Prop) : Splits (P ∗ B) P B :=
  ⟨fun _ holds => holds⟩

/-- The right conjunct is a footprint; the left one is its frame. -/
theorem Splits.there (A P : S → Prop) : Splits (A ∗ P) P A := by
  refine ⟨fun σ holds => ?_⟩
  rw [sepConj_comm] at holds
  exact holds

/-- A footprint inside the left conjunct keeps the right one in its frame. -/
theorem Splits.left {A B P F : S → Prop} (inner : Splits A P F) :
    Splits (A ∗ B) P (F ∗ B) := by
  refine ⟨fun σ holds => ?_⟩
  have regrouped := sepConj_mono inner.elim le_rfl σ holds
  rwa [sepConj_assoc] at regrouped

/-- A footprint inside the right conjunct keeps the left one in its frame. -/
theorem Splits.right {A B P F : S → Prop} (inner : Splits B P F) :
    Splits (A ∗ B) P (A ∗ F) := by
  refine ⟨fun σ holds => ?_⟩
  have regrouped := sepConj_mono le_rfl inner.elim σ holds
  rwa [sepConj_left_comm] at regrouped

/-- A footprint of two conjuncts: split off the first, then the second from
the frame that remains. -/
theorem Splits.sep {T P P' F₁ F : S → Prop} (first : Splits T P F₁) (second : Splits F₁ P' F) :
    Splits T (P ∗ P') F := by
  refine ⟨fun σ holds => ?_⟩
  have regrouped := sepConj_mono le_rfl second.elim σ (first.elim σ holds)
  rwa [← sepConj_assoc] at regrouped

/-- A footprint may be weakened: holding a stronger resource suffices. -/
theorem Splits.weaken {T P P' F : S → Prop} (stronger : P ≤ P') (inner : Splits T P F) :
    Splits T P' F :=
  ⟨fun σ holds => sepConj_mono stronger le_rfl σ (inner.elim σ holds)⟩

/-- The empty footprint: the whole resource is the frame. -/
theorem Splits.emp (T : S → Prop) : Splits T emp T := by
  refine ⟨fun σ holds => ?_⟩
  rw [emp_sepConj]
  exact holds

/-! ## Facts that survive framing -/

/-- **An observation that survives the addition of a separate resource.** -/
def Persistent (O : S → Prop) : Prop :=
  ∀ x y, x ## y → O x → O (x + y)

theorem persistent_pure (φ : Prop) : Persistent (fun _ : S => φ) :=
  fun _ _ _ fact => fact

/-- A persistent observation of the left conjunct holds of the whole. -/
theorem Ensures.left {A B O : S → Prop} (persistent : Persistent O) (inner : Ensures A O) :
    Ensures (A ∗ B) O := by
  refine ⟨?_⟩
  rintro _ ⟨x, y, separate, rfl, holdsA, -⟩
  exact persistent x y separate (inner.elim x holdsA)

/-- A persistent observation of the right conjunct holds of the whole. -/
theorem Ensures.right {A B O : S → Prop} (persistent : Persistent O) (inner : Ensures B O) :
    Ensures (A ∗ B) O := by
  refine ⟨?_⟩
  rintro _ ⟨x, y, separate, rfl, -, holdsB⟩
  rw [SepAlgebra.add_comm separate]
  exact persistent y x (SepAlgebra.separate_symm separate) (inner.elim y holdsB)

/-! ## Entailment -/

/-- **Entailment by splitting**: split the first conjunct of the goal off the
resource, then show the rest. -/
theorem Entails.sep {T A B F : S → Prop} (split : Splits T A F) (rest : Entails F B) :
    Entails T (A ∗ B) :=
  ⟨fun σ holds => sepConj_mono le_rfl rest.elim σ (split.elim σ holds)⟩

/-- **Entailment of one conjunct**: split it off the resource; what remains must
be empty. -/
theorem Entails.atom {T G F : S → Prop} (split : Splits T G F) (rest : Entails F emp) :
    Entails T G := by
  refine ⟨fun σ holds => ?_⟩
  have framed := sepConj_mono le_rfl rest.elim σ (split.elim σ holds)
  rwa [sepConj_emp] at framed

/-- Empty conjuncts make an empty resource. -/
theorem Entails.sepEmp {A B : S → Prop} (left : Entails A emp) (right : Entails B emp) :
    Entails (A ∗ B) emp := by
  refine ⟨fun σ holds => ?_⟩
  have both := sepConj_mono left.elim right.elim σ holds
  rwa [sepConj_emp] at both

/-! ## Iterated conjunctions over a list -/

/-- A member of an iterated conjunction over a list splits off; the other
members are its frame. -/
theorem Splits.bigSep_mem {ι : Type*} [DecidableEq ι] (f : ι → S → Prop) {D : List ι} {i : ι}
    (member : i ∈ D) : Splits (bigSep (D.map f)) (f i) (bigSep ((D.erase i).map f)) := by
  refine ⟨fun σ holds => ?_⟩
  rw [bigSep_perm ((List.perm_cons_erase member).map f), List.map_cons, bigSep_cons] at holds
  exact holds

/-- A persistent observation of one member holds of the iterated conjunction. -/
theorem Ensures.bigSep_mem {ι : Type*} {f : ι → S → Prop} {O : S → Prop} {i : ι}
    (inner : Ensures (f i) O) (persistent : Persistent O) :
    ∀ {D : List ι}, i ∈ D → Ensures (bigSep (D.map f)) O
  | j :: D', member => by
    rw [List.map_cons, bigSep_cons]
    rcases List.mem_cons.mp member with same | later
    · subst same
      exact Ensures.left persistent inner
    · exact Ensures.right persistent (Ensures.bigSep_mem inner persistent later)

end Symbolic

/-! ## Framed calls through a split -/

section Calls

variable {S : Type s} [Zero S] [Add S] [SepAlgebra S]
variable {Op : Type u} {Ret : Op → Type v} {α : Type v}
variable (act : (o : Op) → Action S (Ret o)) [LocalSignature act]

/-- **A framed call through a split**: `spec` needs `P`, the current state
holds `T`, and `T` splits into `P` beside `F`. -/
theorem wp_call_split {T P F : S → Prop} {c : Prog Op Ret α} {R Q : α → S → Prop}
    (spec : Triple act P c R) {σ : S} (holds : T σ) (split : Splits T P F)
    (post : ∀ a σ', (R a ∗ F) σ' → Q a σ') : c.wp act Q σ :=
  wp_call_framed act spec (split.apply holds) post

/-- A framed call through a split that keeps a step invariant of the whole
state. -/
theorem wp_call_split_invariant (G : S → Prop) [StepInvariant act G] {T P F : S → Prop}
    {c : Prog Op Ret α} {R Q : α → S → Prop} (spec : Triple act P c R) {σ : S} (holds : T σ)
    (invariant : G σ) (split : Splits T P F) (post : ∀ a σ', (R a ∗ F) σ' → G σ' → Q a σ') :
    c.wp act Q σ :=
  wp_call_framed_invariant act G spec (split.apply holds) invariant post

end Calls

/-! ## Tactics -/

/-- Atom rules for `sep_split`.  Extend with `macro_rules`. -/
syntax "sep_split_atom" : tactic

macro_rules
  | `(tactic| sep_split_atom) => `(tactic| with_reducible apply Splits.self)

/-- Weakening rules for `sep_split`: replace the footprint by a stronger one
and search again.  Extend with `macro_rules`. -/
syntax "sep_split_weaken" : tactic

macro_rules
  | `(tactic| sep_split_weaken) => `(tactic| fail "sep_split: no conjunct matches the footprint")

/-- The structural search of `sep_split`, through the conjunction tree. -/
syntax "sep_split_struct" : tactic

macro_rules
  | `(tactic| sep_split_struct) => `(tactic| first
      | with_reducible apply Splits.here
      | with_reducible apply Splits.there
      | sep_split_atom
      | (apply Splits.left; sep_split_struct)
      | (apply Splits.right; sep_split_struct))

/-- **Frame inference**: solve `Splits T P ?F`, splitting the footprint `P`
off the resource `T` and choosing the frame `F`.  A footprint of several
conjuncts is split one conjunct at a time. -/
syntax "sep_split" : tactic

macro_rules
  | `(tactic| sep_split) => `(tactic| first
      | sep_split_struct
      | with_reducible apply Splits.emp
      | (apply Splits.sep; sep_split; sep_split)
      | sep_split_weaken)

/-- Membership of a member in the list of an iterated conjunction, through the
members already split off.  Extend with `macro_rules`. -/
syntax "sep_member" : tactic

macro_rules
  | `(tactic| sep_member) => `(tactic| first
      | assumption
      | (refine (List.mem_erase_of_ne ?_).mpr ?_ <;>
          first | assumption | exact Ne.symm ‹_› | sep_member))

macro_rules
  | `(tactic| sep_split_atom) => `(tactic| (apply Splits.bigSep_mem; sep_member))

/-- Persistence of an observation.  Extend with `macro_rules`. -/
syntax "sep_persistent" : tactic

macro_rules
  | `(tactic| sep_persistent) => `(tactic| apply persistent_pure)

/-- Atom rules for `sep_ensures`.  Extend with `macro_rules`. -/
syntax "sep_ensures_atom" : tactic

macro_rules
  | `(tactic| sep_ensures_atom) => `(tactic| with_reducible apply Ensures.pure)

/-- **Framed facts**: solve `Ensures T O`, finding the persistent observation
`O` in one conjunct of `T`, through pure facts and existentials. -/
syntax "sep_ensures" : tactic

macro_rules
  | `(tactic| sep_ensures) => `(tactic| first
      | sep_ensures_atom
      | (apply Ensures.left; sep_persistent; sep_ensures)
      | (apply Ensures.right; sep_persistent; sep_ensures)
      | (apply Ensures.and; sep_ensures)
      | (apply Ensures.exists; intro; sep_ensures))

macro_rules
  | `(tactic| sep_ensures_atom) =>
      `(tactic| (apply Ensures.bigSep_mem; sep_ensures; sep_persistent; sep_member))

/-- Atom rules for `sep_entails`.  Extend with `macro_rules`. -/
syntax "sep_entails_atom" : tactic

macro_rules
  | `(tactic| sep_entails_atom) => `(tactic| apply Entails.refl)

/-- What remains after the last conjunct of an entailment is empty. -/
syntax "sep_entails_emp" : tactic

macro_rules
  | `(tactic| sep_entails_emp) => `(tactic| first
      | with_reducible apply Entails.refl
      | (apply Entails.sepEmp <;> sep_entails_emp))

/-- **Entailment**: solve `Entails T G` by splitting each conjunct of `G` off
`T`, up to the order and grouping of conjuncts and empty conjuncts. -/
syntax "sep_entails" : tactic

macro_rules
  | `(tactic| sep_entails) => `(tactic| first
      | with_reducible apply Entails.refl
      | (apply Entails.sep; sep_split; sep_entails)
      | (apply Entails.atom; sep_split; sep_entails_emp)
      | sep_entails_atom)

/-- Close a goal `G σ` from `h : T σ` by `sep_entails`. -/
macro "sep_exact " h:term : tactic => `(tactic| (refine Entails.apply ?_ $h; sep_entails))

/-- Pull pure facts, existentials and disjunctions out of separating
conjunctions, and drop empty conjuncts. -/
macro "sep_norm" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [sepConj_pure_left, sepConj_pure_right, sepConj_exists_left,
      sepConj_exists_right, sepConj_or_left, sepConj_or_right, sepConj_false_left,
      sepConj_false_right, sepConj_emp, emp_sepConj] $[$loc]?)

section Meta

open Lean Elab Tactic Meta

/-- The signature and the state of a weakest-precondition goal
`Prog.wp act c Q σ`. -/
def wpGoalParts (goal : MVarId) : MetaM (Expr × Expr) := do
  let target ← instantiateMVars (← goal.getType)
  let target ← whnfR target
  unless target.isAppOfArity ``Prog.wp 8 do
    throwError "the goal is not a weakest precondition `Prog.wp act c Q σ`:{indentExpr target}"
  return (target.getArg! 4, target.appArg!)

/-- The state of a weakest-precondition goal. -/
def wpGoalState (goal : MVarId) : MetaM Expr :=
  return (← wpGoalParts goal).2

/-- The hypotheses about the state `σ`, most recent first. -/
def stateHypotheses (σ : Expr) : MetaM (Array Expr) := do
  let mut found := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let type ← instantiateMVars decl.type
    if type.isApp && type.appArg! == σ && (← isProp type) then
      found := found.push decl.toExpr
  return found.reverse

/-- A hypothesis `g : G σ` whose predicate `G` is a step invariant of `act`. -/
def invariantHypothesis? (act σ : Expr) : MetaM (Option Expr) := do
  for g in ← stateHypotheses σ do
    let type ← instantiateMVars (← inferType g)
    try
      let goal ← mkAppM ``StepInvariant #[act, type.appFn!]
      if (← synthInstance? goal).isSome then
        return some g
    catch _ => pure ()
  return none

/-- Run `tac h e` for the hypotheses `e` about `σ` (with `h` its syntax), most
recent first, until one succeeds, and return that hypothesis; otherwise fail
with `what`, the requirement no hypothesis met. -/
def withHypothesisAbout (σ : Expr) (what : MessageData) (tac : Term → Expr → TacticM Unit) :
    TacticM Expr := do
  let candidates ← stateHypotheses σ
  for h in candidates do
    let saved ← saveState
    try
      tac (← Term.exprToSyntax h) h
      return h
    catch _ =>
      saved.restore
  throwError "{what}\nNo hypothesis about the state `{σ}` provides it \
    ({candidates.size} tried)."

/-- **A framed call** of the main weakest-precondition goal `c.wp act Q σ`
through `spec : Triple act P c R`: `P` is split off a hypothesis about `σ`.
The goal becomes `∀ a σ', (R a ∗ F) σ' → Q a σ'` with the frame `F`, or, when
a hypothesis `G σ` holds a step invariant `G`,
`∀ a σ', (R a ∗ F) σ' → G σ' → Q a σ'`.  Returns the hypothesis split and
the invariant hypothesis. -/
def framedCall (spec : Term) (what : MessageData) : TacticM (Expr × Option Expr) :=
  withMainContext do
    let (act, σ) ← wpGoalParts (← getMainGoal)
    let invariant ← invariantHypothesis? act σ
    let used ← withHypothesisAbout σ what fun h _ => do
      match invariant with
      | some g =>
        let g ← Term.exprToSyntax g
        evalTactic (← `(tactic| (apply wp_call_split_invariant _ _ $spec $h $g; sep_split)))
      | none =>
        evalTactic (← `(tactic| (apply wp_call_split _ $spec $h; sep_split)))
    return (used, invariant)

/-- **A framed call**: in a goal `c.wp act Q σ`, use the specification
`spec : Triple act P c R`.  The precondition `P` is split off a hypothesis
about `σ`; the goal becomes `∀ a σ', (R a ∗ F) σ' → Q a σ'` with the frame
`F`.  A hypothesis `G σ` for a step invariant `G` is carried to the new state:
the goal is then `∀ a σ', (R a ∗ F) σ' → G σ' → Q a σ'`. -/
elab "sep_call " spec:term : tactic => do
  discard <| framedCall spec m!"sep_call: the precondition of `{spec}` must split off the state."

end Meta

/-! ## Controls -/

namespace Controls

/-- The bag holding exactly one atom. -/
def single (atom : ℕ) : Multiset ℕ → Prop := fun bag => bag = {atom}

/-- **Positive control**: a footprint in the middle of a conjunction splits
off, with the other two conjuncts as its frame. -/
theorem split_middle :
    Splits (single 1 ∗ (single 2 ∗ single 3)) (single 2) (single 1 ∗ single 3) := by
  sep_split

/-- **Positive control**: entailment up to order and grouping. -/
theorem entails_reordered :
    Entails ((single 1 ∗ single 2) ∗ single 3) (single 3 ∗ (single 1 ∗ single 2)) := by
  sep_entails

/-- **Negative control**: a footprint that is not there does not split off,
whatever the frame. -/
theorem absent_footprint_not_split (F : Multiset ℕ → Prop) :
    ¬ Splits (single 2 ∗ single 3) (single 1) F := by
  intro split
  obtain ⟨x, y, -, sum, one, -⟩ := split.apply (σ := {2} + {3})
    ⟨{2}, {3}, trivial, rfl, rfl, rfl⟩
  have isOne : x = {1} := one
  subst isOne
  have count := congrArg (Multiset.count 1) sum
  simp at count

end Controls

end Mettapedia.GSLT.Logic.AbstractSeparationLogic
