import Mettapedia.GSLT.Logic.ObserverDetermination
import Mettapedia.GSLT.Logic.ObserverPresheaf
import Mettapedia.GSLT.Logic.TypedObservationRelation
import Mettapedia.Logic.TheoryModel.IdentityCarve
import Mettapedia.TypeTheory.Calculi.BooleanSTLC.ObservationalEquality

/-!
# Identity as observation: eliminator observers and observational equality

Observational type theory defines equality by recursion on type formers, and
the saturated relative equivalence of an observer class defines equality by
what the admissible contexts can observe.  This module relates the two on the
closed terms of the boolean calculus.

**The operational theory.**  Terms are closed programs, a closed term together
with its type; nothing reduces, and the equations are syntactic identity.  A
context assigns to every input type a stack of frames: the eliminators
(application to a closed argument, the two projections, case analysis on a
boolean), definable contexts `k [·]` for a closed term `k`, and code observers
that compare the code of the plugged term with a reference code.  An atom
reads a boolean program's value, a proposition's truth, or a program's type.

**The coincidence** (`relEquiv_eliminators_iff`): for the class of eliminator
contexts, the saturated relative equivalence of two closed terms of one type is
exactly their observational equality `ObsEq`: constructor-wise at booleans,
logical equivalence at propositions, componentwise at products and pointwise at
functions.

**The context lemma** (`definable_le_determined`, `relEquiv_definable_iff`):
every definable context preserves the eliminator equivalence, so adding all
definable contexts is conservative.

**Controls.**

* Too few observers identify too much: without application every two functions
  of one type are identified (`dataEliminators_relEquiv_functions`), while the
  eliminators separate the identity from negation.
* Code observers identify too little: they identify at most terms with the
  same code (`code_eq_of_codeObservers_relEquiv`), so they separate the identity
  on booleans from its expansion by case analysis, which are observationally
  equal (`not_codeObservers_relEquiv_idBool`), `⊤` from `⊤ ∧ ⊤`
  (`not_codeObservers_relEquiv_top`), and an η-expansion from its function while
  the eliminators identify them (`eta_observed`); adjoining a code observer to
  the eliminators is a strict extension (`not_relEquiv_sup_quote`), and
  quotation is inadmissible for observational equality in the typed observation
  relation (`code_not_admissible`).
* Typing must be observable: without the atom reading a program's type, the
  eliminators identify `⊥` with `λb. ⊥` and a definable context separates them,
  so the context lemma fails (`not_definable_le_determined_untyped`).
* The coincidence needs observation by evaluation: over a theory that reduces by
  root β-steps, the strong saturated equivalence of the eliminators still implies
  observational equality (`obsEq_of_betaEliminators_relEquiv`) but also counts
  steps, separating `(λx. x) tt` from `tt` (`betaEliminators_separates_redex`).

**Stages.**  At the eliminator stage of the observer presheaf, equality of
classes is observational equality (`stageClass_eliminators_eq_iff`); forgetting
from the definable stage loses nothing, while forgetting to the data-eliminator
stage and from the code stage does lose distinctions; and the diagonal identity
of the stage is thin.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.EliminatorObservers

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.GSLT.AdmissibleContextCongruence.AdmissibleClass
open Mettapedia.TypeTheory.Calculi.BooleanSTLC

/-! ## Saturated equivalence when nothing reduces -/

section Inert

universe uS uContext uRule uAtom

variable {S : GSLT.{uS}} {rules : ContextualRules.{uContext, uRule} S}

/-- **When nothing reduces, the relative equivalence of a class is agreement of
every atom through every admissible context.** -/
theorem relEquiv_iff_of_inert (inert : ∀ source target : S.Term, ¬ S.Step source target)
    (K : AdmissibleClass rules) (observations : ContextualRules.Observations.{uAtom} S)
    (left right : S.Term) :
    K.RelEquiv observations left right ↔
      ∀ context, K.Admissible context → ∀ atom,
        observations.observes atom (rules.plug context left) ↔
          observations.observes atom (rules.plug context right) := by
  constructor
  · intro related context admissible atom
    exact AdmissibleContextCongruence.bisimilar_observes related (atom, ⟨context, admissible⟩)
  · intro agree
    refine ⟨fun left right => ∀ context, K.Admissible context → ∀ atom,
        observations.observes atom (rules.plug context left) ↔
          observations.observes atom (rules.plug context right), ⟨?_, ?_, ?_⟩, agree⟩
    · intro _ _ _ _ _ step
      exact absurd step (inert _ _)
    · intro _ _ _ _ _ step
      exact absurd step (inert _ _)
    · intro _ _ held atom
      exact held atom.2.1 atom.2.2 atom.1

end Inert

/-! ## Frames, stacks and contexts -/

/-- A closed program: a closed term with its type. -/
abbrev Program : Type := (A : Ty) × Closed A

/-- One-step contexts. -/
inductive Frame : Ty → Ty → Type where
  /-- Application to a closed argument: the eliminator of functions. -/
  | apply {A B : Ty} (argument : Closed A) : Frame (.arr A B) B
  /-- The first projection. -/
  | fst {A B : Ty} : Frame (.prod A B) A
  /-- The second projection. -/
  | snd {A B : Ty} : Frame (.prod A B) B
  /-- Case analysis on a boolean: the eliminator of booleans. -/
  | cond {C : Ty} (onTrue onFalse : Closed C) : Frame .bool C
  /-- A definable context `k [·]`. -/
  | host {A B : Ty} (operation : Closed (.arr A B)) : Frame A B
  /-- A code observer: `tt` exactly when the code of the plugged term is the
  reference code. -/
  | quoteEq {A : Ty} (reference : Code) : Frame A .bool

/-- Plug a closed term into a frame. -/
def Frame.plug : {A B : Ty} → Frame A B → Closed A → Closed B
  | _, _, .apply a, t => .app t a
  | _, _, .fst, t => .fst t
  | _, _, .snd, t => .snd t
  | _, _, .cond onTrue onFalse, t => .ite t onTrue onFalse
  | _, _, .host k, t => .app k t
  | _, _, .quoteEq reference, t => if t.code = reference then .tt else .ff

/-- The eliminators of the type formers. -/
inductive Frame.IsEliminator : {A B : Ty} → Frame A B → Prop where
  | apply {A B : Ty} (argument : Closed A) : IsEliminator (.apply (B := B) argument)
  | fst {A B : Ty} : IsEliminator (.fst : Frame (.prod A B) A)
  | snd {A B : Ty} : IsEliminator (.snd : Frame (.prod A B) B)
  | cond {C : Ty} (onTrue onFalse : Closed C) : IsEliminator (.cond onTrue onFalse)

/-- The eliminators of data, without application. -/
inductive Frame.IsDataEliminator : {A B : Ty} → Frame A B → Prop where
  | fst {A B : Ty} : IsDataEliminator (.fst : Frame (.prod A B) A)
  | snd {A B : Ty} : IsDataEliminator (.snd : Frame (.prod A B) B)
  | cond {C : Ty} (onTrue onFalse : Closed C) : IsDataEliminator (.cond onTrue onFalse)

/-- The definable frames: eliminators and closed contexts `k [·]`. -/
inductive Frame.IsDefinable : {A B : Ty} → Frame A B → Prop where
  | eliminator {A B : Ty} {frame : Frame A B} : frame.IsEliminator → IsDefinable frame
  | host {A B : Ty} (operation : Closed (.arr A B)) : IsDefinable (.host operation)

/-- The eliminators together with the code observers. -/
inductive Frame.IsCodeOrEliminator : {A B : Ty} → Frame A B → Prop where
  | eliminator {A B : Ty} {frame : Frame A B} : frame.IsEliminator → IsCodeOrEliminator frame
  | quoteEq {A : Ty} (reference : Code) : IsCodeOrEliminator (.quoteEq (A := A) reference)

theorem Frame.IsDataEliminator.isEliminator {A B : Ty} {frame : Frame A B}
    (data : frame.IsDataEliminator) : frame.IsEliminator := by
  cases data with
  | fst => exact .fst
  | snd => exact .snd
  | cond onTrue onFalse => exact .cond onTrue onFalse

/-- Stacks of frames; the first frame is applied first. -/
inductive Stack : Ty → Ty → Type where
  | nil {A : Ty} : Stack A A
  | cons {A B C : Ty} (frame : Frame A B) (rest : Stack B C) : Stack A C

/-- Plug a closed term into a stack. -/
def Stack.plug : {A C : Ty} → Stack A C → Closed A → Closed C
  | _, _, .nil, t => t
  | _, _, .cons frame rest, t => rest.plug (frame.plug t)

/-- Concatenation of stacks. -/
def Stack.append : {A B C : Ty} → Stack A B → Stack B C → Stack A C
  | _, _, _, .nil, later => later
  | _, _, _, .cons frame rest, later => .cons frame (rest.append later)

theorem Stack.plug_append {A B C : Ty} (earlier : Stack A B) (later : Stack B C) (t : Closed A) :
    (earlier.append later).plug t = later.plug (earlier.plug t) := by
  induction earlier with
  | nil => rfl
  | cons frame rest ih => exact ih later (frame.plug t)

/-- Every frame of a stack satisfies a predicate. -/
inductive Stack.All (P : ∀ {A B : Ty}, Frame A B → Prop) : {A C : Ty} → Stack A C → Prop where
  | nil {A : Ty} : Stack.All P (.nil : Stack A A)
  | cons {A B C : Ty} {frame : Frame A B} {rest : Stack B C} :
      P frame → Stack.All P rest → Stack.All P (.cons frame rest)

theorem Stack.All.append {P : ∀ {A B : Ty}, Frame A B → Prop} {A B C : Ty}
    {earlier : Stack A B} {later : Stack B C} (first : earlier.All P) (second : later.All P) :
    (earlier.append later).All P := by
  induction first with
  | nil => exact second
  | cons head _ ih => exact .cons head (ih second)

theorem Stack.All.mono {P Q : ∀ {A B : Ty}, Frame A B → Prop}
    (implies : ∀ {A B : Ty} (frame : Frame A B), P frame → Q frame) {A C : Ty} {stack : Stack A C}
    (all : stack.All P) : stack.All Q := by
  induction all with
  | nil => exact .nil
  | cons head _ ih => exact .cons (implies _ head) ih

/-- A context: a stack of frames out of every type.  Terms are only ever
compared with terms of the same type, so each type receives its own
experiment. -/
def Context : Type := (A : Ty) → (B : Ty) × Stack A B

def Context.identity : Context := fun A => ⟨A, .nil⟩

def Context.compose (outer inner : Context) : Context := fun A =>
  ⟨(outer (inner A).1).1, (inner A).2.append (outer (inner A).1).2⟩

def Context.plug (context : Context) (program : Program) : Program :=
  ⟨(context program.1).1, (context program.1).2.plug program.2⟩

theorem Context.plug_compose (outer inner : Context) (program : Program) :
    (outer.compose inner).plug program = outer.plug (inner.plug program) :=
  congrArg (Sigma.mk _) (Stack.plug_append _ _ _)

/-- The context applying one stack at its input type, and nothing elsewhere. -/
def Context.single {A B : Ty} (stack : Stack A B) : Context := fun X =>
  if h : X = A then ⟨B, h ▸ stack⟩ else ⟨X, .nil⟩

theorem Context.plug_single {A B : Ty} (stack : Stack A B) (t : Closed A) :
    (Context.single stack).plug ⟨A, t⟩ = ⟨B, stack.plug t⟩ := by
  unfold Context.plug Context.single
  rw [dif_pos rfl]

theorem Context.all_single {P : ∀ {A B : Ty}, Frame A B → Prop} {A B : Ty} {stack : Stack A B}
    (all : stack.All P) (X : Ty) : ((Context.single stack) X).2.All P := by
  unfold Context.single
  by_cases h : X = A
  · subst h
    rw [dif_pos rfl]
    exact all
  · rw [dif_neg h]
    exact .nil

/-! ## The operational theory -/

/-- Closed programs up to syntactic identity; nothing reduces. -/
def programGSLT : GSLT where
  Term := Program
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites _ _ := False
  rewrites_resp_left := fun _ step => step.elim
  rewrites_resp_right := fun step _ => step.elim

theorem programGSLT_inert (source target : Program) : ¬ programGSLT.Step source target :=
  fun step => step

/-- Contexts as stacks of frames, with no authored rules. -/
def rules : ContextualRules programGSLT where
  Context := Context
  identity := Context.identity
  compose := Context.compose
  plug := Context.plug
  plug_identity _ := rfl
  plug_compose := Context.plug_compose
  plug_resp _ _ _ equal := congrArg _ equal
  Rule := Empty
  fires rule _ _ := rule.elim
  fires_resp_left := by intro rule; exact rule.elim
  fires_resp_right := by intro rule; exact rule.elim
  fires_step := by intro rule; exact rule.elim

/-- Atoms: a boolean program computes `true`; a proposition holds; a program has
a given type. -/
inductive Atom where
  | isTrue
  | holds
  | ofType (A : Ty)

def observes : Atom → Program → Prop
  | .isTrue, ⟨.bool, t⟩ => t.value = true
  | .holds, ⟨.prop, t⟩ => t.value
  | .ofType A, ⟨B, _⟩ => B = A
  | _, _ => False

def observations : ContextualRules.Observations programGSLT where
  Atom := Atom
  observes := observes
  observes_resp _ _ _ equal := by
    change _ = _ at equal
    rw [equal]

/-! ## Observer classes -/

/-- The class of contexts all of whose frames satisfy a predicate. -/
def frameClass (P : ∀ {A B : Ty}, Frame A B → Prop) : AdmissibleClass rules where
  Admissible context := ∀ A, (context A).2.All P
  identity_mem := fun _ => .nil
  compose_mem := fun outer inner A => Stack.All.append (inner A) (outer _)

theorem frameClass_mono {P Q : ∀ {A B : Ty}, Frame A B → Prop}
    (implies : ∀ {A B : Ty} (frame : Frame A B), P frame → Q frame) :
    frameClass P ≤ frameClass Q :=
  fun _ admissible A => (admissible A).mono implies

/-- The eliminator observers. -/
def eliminators : AdmissibleClass rules := frameClass Frame.IsEliminator

/-- The data eliminators: projections and case analysis, without application. -/
def dataEliminators : AdmissibleClass rules := frameClass Frame.IsDataEliminator

/-- The definable contexts. -/
def definable : AdmissibleClass rules := frameClass Frame.IsDefinable

/-- The eliminators together with the code observers. -/
def codeObservers : AdmissibleClass rules := frameClass Frame.IsCodeOrEliminator

theorem dataEliminators_le_eliminators : dataEliminators ≤ eliminators :=
  frameClass_mono fun _ data => data.isEliminator

theorem eliminators_le_definable : eliminators ≤ definable :=
  frameClass_mono fun _ eliminator => .eliminator eliminator

theorem eliminators_le_codeObservers : eliminators ≤ codeObservers :=
  frameClass_mono fun _ eliminator => .eliminator eliminator

theorem relEquiv_iff (K : AdmissibleClass rules) (left right : Program) :
    K.RelEquiv observations left right ↔
      ∀ context, K.Admissible context → ∀ atom,
        observes atom (context.plug left) ↔ observes atom (context.plug right) :=
  relEquiv_iff_of_inert programGSLT_inert K observations left right

/-! ## Observational equality is preserved by the definable frames -/

/-- Observationally equal programs of one type agree on every atom. -/
theorem observes_iff_of_obsEq {B : Ty} {x y : Closed B} (related : ObsEq B x y) (atom : Atom) :
    observes atom ⟨B, x⟩ ↔ observes atom ⟨B, y⟩ := by
  cases atom with
  | isTrue =>
      cases B with
      | bool => exact Iff.of_eq (congrArg (fun b : Bool => b = true) related)
      | prop => exact Iff.rfl
      | prod _ _ => exact Iff.rfl
      | arr _ _ => exact Iff.rfl
  | holds =>
      cases B with
      | bool => exact Iff.rfl
      | prop => exact related
      | prod _ _ => exact Iff.rfl
      | arr _ _ => exact Iff.rfl
  | ofType _ => exact Iff.rfl

theorem ObsEq.framePlug_of_eliminator {A B : Ty} {frame : Frame A B}
    (eliminator : frame.IsEliminator) {t u : Closed A} (related : ObsEq A t u) :
    ObsEq B (frame.plug t) (frame.plug u) := by
  cases eliminator with
  | apply argument => exact related argument
  | fst => exact related.1
  | snd => exact related.2
  | cond onTrue onFalse =>
      apply ObsEq.of_value_eq
      show cond t.value onTrue.value onFalse.value = cond u.value onTrue.value onFalse.value
      rw [show t.value = u.value from related]

theorem ObsEq.framePlug_of_definable {A B : Ty} {frame : Frame A B}
    (definableFrame : frame.IsDefinable) {t u : Closed A} (related : ObsEq A t u) :
    ObsEq B (frame.plug t) (frame.plug u) := by
  cases definableFrame with
  | eliminator eliminator => exact ObsEq.framePlug_of_eliminator eliminator related
  | host operation => exact related.app_right operation

theorem ObsEq.stackPlug {P : ∀ {A B : Ty}, Frame A B → Prop}
    (preserves : ∀ {A B : Ty} {frame : Frame A B}, P frame →
      ∀ {t u : Closed A}, ObsEq A t u → ObsEq B (frame.plug t) (frame.plug u))
    {A C : Ty} {stack : Stack A C} (all : stack.All P) {t u : Closed A}
    (related : ObsEq A t u) : ObsEq C (stack.plug t) (stack.plug u) := by
  induction all with
  | nil => exact related
  | cons head _ ih => exact ih (preserves head related)

/-! ## The coincidence theorem -/

/-- Agreement of every atom after every eliminator stack. -/
def StackAgree (A : Ty) (t u : Closed A) : Prop :=
  ∀ (B : Ty) (stack : Stack A B), stack.All Frame.IsEliminator →
    ∀ atom, observes atom ⟨B, stack.plug t⟩ ↔ observes atom ⟨B, stack.plug u⟩

theorem stackAgree_of_relEquiv {A : Ty} {t u : Closed A}
    (related : eliminators.RelEquiv observations ⟨A, t⟩ ⟨A, u⟩) : StackAgree A t u := by
  intro B stack all atom
  have agree := (relEquiv_iff eliminators _ _).mp related (Context.single stack)
    (Context.all_single all) atom
  rwa [Context.plug_single, Context.plug_single] at agree

theorem obsEq_of_stackAgree : ∀ {A : Ty} {t u : Closed A}, StackAgree A t u → ObsEq A t u
  | .bool, t, u, agree => by
      have truth := agree .bool .nil .nil .isTrue
      exact Bool.eq_iff_iff.mpr truth
  | .prop, _, _, agree => agree .prop .nil .nil .holds
  | .prod _ _, _, _, agree =>
      ⟨obsEq_of_stackAgree fun B stack all => agree B (.cons .fst stack) (.cons .fst all),
        obsEq_of_stackAgree fun B stack all => agree B (.cons .snd stack) (.cons .snd all)⟩
  | .arr _ _, _, _, agree => fun a =>
      obsEq_of_stackAgree fun B stack all =>
        agree B (.cons (.apply a) stack) (.cons (.apply a) all)

theorem relEquiv_of_obsEq {A : Ty} {t u : Closed A} (related : ObsEq A t u) :
    eliminators.RelEquiv observations ⟨A, t⟩ ⟨A, u⟩ := by
  refine (relEquiv_iff eliminators _ _).mpr fun context admissible atom => ?_
  exact observes_iff_of_obsEq
    (ObsEq.stackPlug (fun eliminator => ObsEq.framePlug_of_eliminator eliminator)
      (admissible A) related) atom

/-- **Identity as observation.**  For closed terms of one type, the saturated
relative equivalence of the eliminator observers is observational equality,
defined by recursion on type formers. -/
theorem relEquiv_eliminators_iff {A : Ty} (t u : Closed A) :
    eliminators.RelEquiv observations ⟨A, t⟩ ⟨A, u⟩ ↔ ObsEq A t u :=
  ⟨fun related => obsEq_of_stackAgree (stackAgree_of_relEquiv related), relEquiv_of_obsEq⟩

/-- Every class separates programs of different types. -/
theorem type_eq_of_relEquiv (K : AdmissibleClass rules) {left right : Program}
    (related : K.RelEquiv observations left right) : left.1 = right.1 := by
  have agree := (relEquiv_iff K left right).mp related Context.identity K.identity_mem
    (.ofType left.1)
  exact (agree.mp rfl).symm

/-! ## The context lemma, in the observer lattice -/

/-- **Every definable context preserves the eliminator equivalence.** -/
theorem definable_le_determined : definable ≤ eliminators.determined observations := by
  intro context admissible left right related
  obtain ⟨A, t⟩ := left
  obtain ⟨A', u⟩ := right
  have same : A = A' := type_eq_of_relEquiv eliminators related
  subst same
  have obs := (relEquiv_eliminators_iff t u).mp related
  exact relEquiv_of_obsEq
    (ObsEq.stackPlug (fun definableFrame => ObsEq.framePlug_of_definable definableFrame)
      (admissible A) obs)

/-- **Context lemma.**  The definable contexts identify exactly what the
eliminators identify. -/
theorem relEquiv_definable_iff (left right : Program) :
    definable.RelEquiv observations left right ↔ eliminators.RelEquiv observations left right :=
  (AdmissibleClass.relEquiv_iff_iff_le_determined observations eliminators_le_definable).mpr
    definable_le_determined left right

/-! ## Control: too few observers identify too much -/

theorem dataEliminator_stack_arr_agree {A B C : Ty} (stack : Stack (.arr A B) C)
    (all : stack.All Frame.IsDataEliminator) (f g : Closed (.arr A B)) (atom : Atom) :
    observes atom ⟨C, stack.plug f⟩ ↔ observes atom ⟨C, stack.plug g⟩ := by
  cases all with
  | nil =>
      cases atom with
      | isTrue => exact Iff.rfl
      | holds => exact Iff.rfl
      | ofType _ => exact Iff.rfl
  | cons head _ => cases head

/-- **Without application, every two functions of one type are identified.** -/
theorem dataEliminators_relEquiv_functions {A B : Ty} (f g : Closed (.arr A B)) :
    dataEliminators.RelEquiv observations ⟨_, f⟩ ⟨_, g⟩ :=
  (relEquiv_iff dataEliminators _ _).mpr fun _ admissible atom =>
    dataEliminator_stack_arr_agree _ (admissible _) f g atom

/-- The eliminators separate the identity on booleans from negation, which the
data eliminators identify. -/
theorem too_few_observers :
    dataEliminators.RelEquiv observations ⟨_, Examples.idBool⟩ ⟨_, Examples.notBool⟩ ∧
      ¬ eliminators.RelEquiv observations ⟨_, Examples.idBool⟩ ⟨_, Examples.notBool⟩ :=
  ⟨dataEliminators_relEquiv_functions _ _, fun related =>
    Examples.not_obsEq_idBool_notBool ((relEquiv_eliminators_iff _ _).mp related)⟩

/-! ## Control: code observers identify too little -/

/-- The code observer comparing with the code of the identity on booleans. -/
def quoteIdBool : Context :=
  Context.single (.cons (.quoteEq (A := .arr .bool .bool) Examples.idBool.code) .nil)

theorem quoteIdBool_admissible : codeObservers.Admissible quoteIdBool :=
  Context.all_single (.cons (.quoteEq _) .nil)

theorem plug_quoteIdBool_idBool :
    quoteIdBool.plug ⟨_, Examples.idBool⟩ = ⟨.bool, .tt⟩ := by
  unfold quoteIdBool
  rw [Context.plug_single]
  show (⟨Ty.bool, if Examples.idBool.code = Examples.idBool.code then .tt else .ff⟩ : Program) = _
  rw [if_pos rfl]

theorem plug_quoteIdBool_condIdBool :
    quoteIdBool.plug ⟨_, Examples.condIdBool⟩ = ⟨.bool, .ff⟩ := by
  unfold quoteIdBool
  rw [Context.plug_single]
  show (⟨Ty.bool, if Examples.condIdBool.code = Examples.idBool.code then .tt else .ff⟩ : Program) =
    _
  rw [if_neg (Ne.symm Examples.idBool_code_ne)]

/-- **A code observer separates two observationally equal terms.** -/
theorem not_codeObservers_relEquiv_idBool :
    ¬ codeObservers.RelEquiv observations ⟨_, Examples.idBool⟩ ⟨_, Examples.condIdBool⟩ := by
  intro related
  have agree := (relEquiv_iff codeObservers _ _).mp related quoteIdBool
    quoteIdBool_admissible .isTrue
  rw [plug_quoteIdBool_idBool, plug_quoteIdBool_condIdBool] at agree
  exact Bool.noConfusion (agree.mp rfl : (false : Bool) = true)

/-- The eliminators identify the same pair. -/
theorem eliminators_relEquiv_idBool :
    eliminators.RelEquiv observations ⟨_, Examples.idBool⟩ ⟨_, Examples.condIdBool⟩ :=
  (relEquiv_eliminators_iff _ _).mpr Examples.obsEq_idBool_condIdBool

/-- **Adjoining the code observer to the eliminators is a strict extension**: it
separates a pair the eliminators identify. -/
theorem not_relEquiv_sup_quote :
    ¬ (eliminators ⊔ AdmissibleClass.generatedBy {quoteIdBool}).RelEquiv observations
      ⟨_, Examples.idBool⟩ ⟨_, Examples.condIdBool⟩ := by
  refine AdmissibleClass.not_relEquiv_sup_of_not_preserved observations eliminators
    (Set.mem_singleton quoteIdBool) ?_
  change ¬ eliminators.RelEquiv observations (quoteIdBool.plug ⟨_, Examples.idBool⟩)
    (quoteIdBool.plug ⟨_, Examples.condIdBool⟩)
  rw [plug_quoteIdBool_idBool, plug_quoteIdBool_condIdBool, relEquiv_eliminators_iff]
  exact fun same => Bool.noConfusion (same : (true : Bool) = false)

/-- The code observer is outside the class determined by the eliminators. -/
theorem quoteIdBool_not_determined :
    ¬ (eliminators.determined observations).Admissible quoteIdBool := by
  intro preserves
  have image := preserves eliminators_relEquiv_idBool
  change eliminators.RelEquiv observations (quoteIdBool.plug ⟨_, Examples.idBool⟩)
    (quoteIdBool.plug ⟨_, Examples.condIdBool⟩) at image
  rw [plug_quoteIdBool_idBool, plug_quoteIdBool_condIdBool, relEquiv_eliminators_iff] at image
  exact Bool.noConfusion (image : (true : Bool) = false)

/-- The code observer comparing with the code of `⊤`. -/
def quoteTop : Context :=
  Context.single (.cons (.quoteEq (A := .prop) (Tm.top : Closed .prop).code) .nil)

/-- **A structural observer on propositions separates `⊤` from `⊤ ∧ ⊤`**, which
are logically equivalent: code observers break propositional
extensionality. -/
theorem not_codeObservers_relEquiv_top :
    ¬ codeObservers.RelEquiv observations ⟨.prop, .top⟩ ⟨.prop, .and .top .top⟩ := by
  intro related
  have agree := (relEquiv_iff codeObservers _ _).mp related quoteTop
    (Context.all_single (.cons (.quoteEq _) .nil)) .isTrue
  unfold quoteTop at agree
  rw [Context.plug_single, Context.plug_single] at agree
  change ((if (Tm.top : Closed .prop).code = (Tm.top : Closed .prop).code then Tm.tt else Tm.ff :
      Closed .bool).value = true) ↔
    ((if (Tm.and .top .top : Closed .prop).code = (Tm.top : Closed .prop).code then Tm.tt
      else Tm.ff : Closed .bool).value = true) at agree
  rw [if_pos rfl, if_neg (Ne.symm Examples.top_code_ne_andTopTop)] at agree
  exact Bool.noConfusion (agree.mp rfl : (false : Bool) = true)

theorem eliminators_relEquiv_top :
    eliminators.RelEquiv observations ⟨.prop, .top⟩ ⟨.prop, .and .top .top⟩ :=
  (relEquiv_eliminators_iff _ _).mpr Examples.obsEq_top_andTopTop

/-- **Quotation is inadmissible for observational equality** in the typed
observation relation: codes observed by equality separate the identity from its
expansion by case analysis. -/
theorem code_not_admissible :
    ¬ TypedObservation.Admissible (Carrier := fun _ : Unit => Code)
      (ObsEq (.arr .bool .bool)) (TypedObservation.equalityChoice (fun _ : Unit => Code))
      (.arrow .proc (.ground ())) (fun t : Closed (.arr .bool .bool) => t.code) :=
  TypedObservation.quote_not_admissible (ObsEq (.arr .bool .bool))
    (TypedObservation.equalityChoice (fun _ : Unit => Code)) (fun _ _ => Iff.rfl)
    (fun t : Closed (.arr .bool .bool) => t.code) Examples.obsEq_idBool_condIdBool
    Examples.idBool_code_ne

/-! ## Control: typing must be observable

The atom `ofType` lets every class separate programs of different types.  It is
needed: with only the ground atoms, the eliminators identify the false
proposition `⊥` with the function `λb. ⊥`, since neither has an observable
outcome under any eliminator, while the definable context `(λp. tt) [·]` sends
the first to `tt` and leaves the second unobservable.  The definable contexts
then fall outside the determined class (`not_definable_le_determined_untyped`). -/

/-- The ground atoms alone. -/
inductive GroundAtom where
  | isTrue
  | holds

def groundObserves : GroundAtom → Program → Prop
  | .isTrue, ⟨.bool, t⟩ => t.value = true
  | .holds, ⟨.prop, t⟩ => t.value
  | _, _ => False

def untypedObservations : ContextualRules.Observations programGSLT where
  Atom := GroundAtom
  observes := groundObserves
  observes_resp _ _ _ equal := by
    change _ = _ at equal
    rw [equal]

theorem eliminator_stack_prop_nil {C : Ty} (stack : Stack .prop C)
    (all : stack.All Frame.IsEliminator) (t : Closed .prop) :
    (⟨C, stack.plug t⟩ : Program) = ⟨.prop, t⟩ := by
  cases all with
  | nil => rfl
  | cons head _ => cases head

theorem groundObserves_bot (atom : GroundAtom) : ¬ groundObserves atom ⟨.prop, .bot⟩ := by
  cases atom with
  | isTrue => exact fun h => h
  | holds => exact fun h => h

theorem groundObserves_constBot {C : Ty} (stack : Stack (.arr .bool .prop) C)
    (all : stack.All Frame.IsEliminator) (atom : GroundAtom) :
    ¬ groundObserves atom ⟨C, stack.plug (.lam .bot)⟩ := by
  cases all with
  | nil =>
      cases atom with
      | isTrue => exact fun h => h
      | holds => exact fun h => h
  | @cons _ _ _ frame rest head restAll =>
      cases head with
      | apply argument =>
          show ¬ groundObserves atom ⟨_, rest.plug (.app (.lam .bot) argument)⟩
          rw [eliminator_stack_prop_nil rest restAll]
          cases atom with
          | isTrue => exact fun h => h
          | holds => exact fun h => h

/-- Without the type atom, the eliminators identify `⊥` with `λb. ⊥`. -/
theorem eliminators_untyped_relEquiv_bot :
    eliminators.RelEquiv untypedObservations ⟨.prop, .bot⟩ ⟨.arr .bool .prop, .lam .bot⟩ := by
  refine (relEquiv_iff_of_inert programGSLT_inert eliminators untypedObservations _ _).mpr ?_
  intro context admissible atom
  change groundObserves atom (context.plug ⟨.prop, .bot⟩) ↔
    groundObserves atom (context.plug ⟨.arr .bool .prop, .lam .bot⟩)
  unfold Context.plug
  rw [eliminator_stack_prop_nil _ (admissible .prop)]
  exact iff_of_false (groundObserves_bot atom) (groundObserves_constBot _ (admissible _) atom)

/-- The definable context `(λp. tt) [·]` at `prop`. -/
def constTrueAtProp : Context :=
  Context.single (.cons (.host (.lam .tt : Closed (.arr .prop .bool))) .nil)

/-- **Without the type atom, a definable context is not determined by the
eliminators.** -/
theorem not_definable_le_determined_untyped :
    ¬ definable ≤ eliminators.determined untypedObservations := by
  intro le
  have preserves := le constTrueAtProp (Context.all_single (.cons (.host _) .nil))
    eliminators_untyped_relEquiv_bot
  have agree := (relEquiv_iff_of_inert programGSLT_inert eliminators untypedObservations _ _).mp
    preserves Context.identity eliminators.identity_mem .isTrue
  change groundObserves .isTrue (constTrueAtProp.plug ⟨.prop, .bot⟩) ↔
    groundObserves .isTrue (constTrueAtProp.plug ⟨.arr .bool .prop, .lam .bot⟩) at agree
  have left : constTrueAtProp.plug ⟨.prop, .bot⟩ = ⟨.bool, .app (.lam .tt) .bot⟩ :=
    Context.plug_single _ _
  have right : constTrueAtProp.plug ⟨.arr .bool .prop, .lam .bot⟩ =
      ⟨.arr .bool .prop, .lam .bot⟩ := by
    unfold constTrueAtProp Context.plug Context.single
    rw [dif_neg (by decide)]
    rfl
  rw [left, right] at agree
  exact agree.mp rfl

/-! ## Code observers see codes -/

/-- The code observer comparing with the code of `t`. -/
def quoteContext {A : Ty} (t : Closed A) : Context :=
  Context.single (.cons (.quoteEq (A := A) t.code) .nil)

theorem quoteContext_admissible {A : Ty} (t : Closed A) :
    codeObservers.Admissible (quoteContext t) :=
  Context.all_single (.cons (.quoteEq _) .nil)

theorem plug_quoteContext_self {A : Ty} (t : Closed A) :
    (quoteContext t).plug ⟨A, t⟩ = ⟨.bool, .tt⟩ := by
  unfold quoteContext
  rw [Context.plug_single]
  show (⟨Ty.bool, if t.code = t.code then .tt else .ff⟩ : Program) = _
  rw [if_pos rfl]

theorem plug_quoteContext_of_ne {A : Ty} {t u : Closed A} (different : u.code ≠ t.code) :
    (quoteContext t).plug ⟨A, u⟩ = ⟨.bool, .ff⟩ := by
  unfold quoteContext
  rw [Context.plug_single]
  show (⟨Ty.bool, if u.code = t.code then .tt else .ff⟩ : Program) = _
  rw [if_neg different]

/-- **Code observers identify at most terms with the same code.** -/
theorem code_eq_of_codeObservers_relEquiv {A : Ty} {t u : Closed A}
    (related : codeObservers.RelEquiv observations ⟨A, t⟩ ⟨A, u⟩) : t.code = u.code := by
  refine Decidable.byContradiction fun different => ?_
  have agree := (relEquiv_iff codeObservers _ _).mp related (quoteContext t)
    (quoteContext_admissible t) .isTrue
  rw [plug_quoteContext_self, plug_quoteContext_of_ne (Ne.symm different)] at agree
  exact Bool.noConfusion (agree.mp rfl : (false : Bool) = true)

/-- **Extensionality is observed.**  The eliminators identify an η-expansion with
its function; the code observers separate them.  This is the typed, closed
counterpart of the β-observer against the βη-observer on `λx. y x` and `y`. -/
theorem eta_observed :
    eliminators.RelEquiv observations ⟨_, Examples.etaExpand Examples.idBool⟩
        ⟨_, Examples.idBool⟩ ∧
      ¬ codeObservers.RelEquiv observations ⟨_, Examples.etaExpand Examples.idBool⟩
        ⟨_, Examples.idBool⟩ :=
  ⟨(relEquiv_eliminators_iff _ _).mpr (Examples.obsEq_etaExpand _), fun related =>
    Examples.etaExpand_idBool_code_ne (code_eq_of_codeObservers_relEquiv related)⟩

/-! ## Control: a presentation that counts reduction steps

The coincidence is a statement about observation by evaluation: nothing
reduces, and the atoms read what a program computes.  If instead the theory
reduces by one root β-step and the saturated equivalence is strong
bisimilarity, the eliminators still see everything observational equality sees
(`obsEq_of_betaEliminators_relEquiv`), but they also count steps:
`(λx. x) tt` and `tt` are observationally equal and separated
(`betaEliminators_separates_redex`). -/

/-- One root β-step. -/
inductive RootBeta : Program → Program → Prop where
  | beta {A B : Ty} (body : Tm [A] B) (argument : Closed A) :
      RootBeta ⟨B, .app (.lam body) argument⟩ ⟨B, body.fill argument⟩

/-- Closed programs reducing by root β-steps. -/
def betaGSLT : GSLT where
  Term := Program
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := RootBeta
  rewrites_resp_left := fun {_ _ target} equal step => ⟨target, equal ▸ step, rfl⟩
  rewrites_resp_right := fun step equal => equal ▸ step

def betaRules : ContextualRules betaGSLT where
  Context := Context
  identity := Context.identity
  compose := Context.compose
  plug := Context.plug
  plug_identity _ := rfl
  plug_compose := Context.plug_compose
  plug_resp _ _ _ equal := congrArg _ equal
  Rule := Empty
  fires rule _ _ := rule.elim
  fires_resp_left := by intro rule; exact rule.elim
  fires_resp_right := by intro rule; exact rule.elim
  fires_step := by intro rule; exact rule.elim

def betaObservations : ContextualRules.Observations betaGSLT where
  Atom := Atom
  observes := observes
  observes_resp _ _ _ equal := by
    change _ = _ at equal
    rw [equal]

/-- The eliminator contexts over the stepping theory. -/
def betaEliminators : AdmissibleClass betaRules where
  Admissible context := ∀ A, (context A).2.All Frame.IsEliminator
  identity_mem := fun _ => .nil
  compose_mem := fun outer inner A => Stack.All.append (inner A) (outer _)

/-- The stepping presentation sees at least what observational equality
sees. -/
theorem obsEq_of_betaEliminators_relEquiv {A : Ty} {t u : Closed A}
    (related : betaEliminators.RelEquiv betaObservations ⟨A, t⟩ ⟨A, u⟩) : ObsEq A t u := by
  refine obsEq_of_stackAgree fun B stack all atom => ?_
  have agree := AdmissibleContextCongruence.bisimilar_observes related
    (atom, ⟨Context.single stack, Context.all_single all⟩)
  change observes atom ((Context.single stack).plug ⟨A, t⟩) ↔
    observes atom ((Context.single stack).plug ⟨A, u⟩) at agree
  rwa [Context.plug_single, Context.plug_single] at agree

theorem no_step_tt (target : Program) : ¬ RootBeta ⟨.bool, .tt⟩ target := by
  intro step
  cases step

/-- **Counting steps separates observationally equal terms.** -/
theorem betaEliminators_separates_redex :
    ObsEq .bool (.app Examples.idBool .tt) .tt ∧
      ¬ betaEliminators.RelEquiv betaObservations ⟨.bool, .app Examples.idBool .tt⟩ ⟨.bool, .tt⟩ := by
  refine ⟨rfl, fun related => ?_⟩
  obtain ⟨_, step, _⟩ := AdmissibleContextCongruence.bisimilar_forward related
    ⟨Context.identity, betaEliminators.identity_mem⟩
    (show RootBeta ⟨.bool, .app (.lam (.var .zero)) .tt⟩ _ from .beta (.var .zero) .tt)
  exact no_step_tt _ step

/-! ## Stages of the observer presheaf -/

/-- **At the eliminator stage, identity is observational equality.** -/
theorem stageClass_eliminators_eq_iff {A : Ty} (t u : Closed A) :
    stageClass observations eliminators ⟨A, t⟩ = stageClass observations eliminators ⟨A, u⟩ ↔
      ObsEq A t u :=
  (stageClass_eq_iff observations eliminators _ _).trans (relEquiv_eliminators_iff t u)

/-- Forgetting from the definable stage to the eliminator stage loses nothing. -/
theorem restrict_definable_injective :
    Function.Injective (restrict observations eliminators_le_definable) :=
  (restrict_injective_iff observations eliminators_le_definable).mpr fun left right related =>
    (relEquiv_definable_iff left right).mpr related

/-- Forgetting from the eliminator stage to the data-eliminator stage loses the
distinction between the identity and negation. -/
theorem restrict_dataEliminators_not_injective :
    ¬ Function.Injective (restrict observations dataEliminators_le_eliminators) := fun injective =>
  too_few_observers.2
    ((restrict_injective_iff observations dataEliminators_le_eliminators).mp injective _ _
      too_few_observers.1)

/-- Forgetting from the code stage to the eliminator stage loses the distinction
between two codes of the identity. -/
theorem restrict_codeObservers_not_injective :
    ¬ Function.Injective (restrict observations eliminators_le_codeObservers) := fun injective =>
  not_codeObservers_relEquiv_idBool
    ((restrict_injective_iff observations eliminators_le_codeObservers).mp injective _ _
      eliminators_relEquiv_idBool)

open Mettapedia.Logic.TheoryModel.IdentityProofs in
/-- The diagonal identity of the eliminator stage is thin: all its proofs of an
equation are equal. -/
theorem eliminatorStage_identity_uip :
    (presheafIdentity (observerPresheaf observations) (Opposite.op eliminators)).Sat .uip :=
  presheafIdentity_sat_uip _ _

end Mettapedia.GSLT.EliminatorObservers
