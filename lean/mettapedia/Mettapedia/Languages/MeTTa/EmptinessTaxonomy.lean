import Mettapedia.GSLT.Core.Separation
import Mettapedia.GSLT.Core.ObservationIndexedPruning

/-!
# A taxonomy of emptinesses, and which of them may share a spelling

Several unrelated notions get called *empty*, and designs keep trying to give
some of them one symbol.  This module fixes a small language in which the
notions can all be written down, and then decides the sharing question by the
criterion of `Core.Separation`: two notions may share a spelling exactly when
no context tells them apart.

The kinds distinguished here are

* **zero outcomes** — a computation with no answers.  An effect, not a value.
* **the unit datum** `()` — exactly one answer, itself.
* **the empty collection** — one answer, which happens to be a container
  with nothing in it.
* **an inert symbol** — one answer, an uninterpreted atom.  In particular an
  atom that happens to be *spelled* `Empty`.
* **a fault** — one answer, reporting that the question was broken.

Four of the five produce one answer and differ only in which; the first
produces none.  That is the whole distinction, and every measured leak comes
from erasing it.

The central result is a dichotomy.  Suppose a design wants the symbol `Empty`
to mean zero outcomes while remaining writable as data.  Then:

* if the reading is applied wherever the symbol occurs, the symbol becomes
  **indistinguishable from zero in every context** — it is a redundant
  spelling that can never be observed, so it carries no data
  (`uniform_makes_atom_redundant`); or
* if the reading is applied only where results are returned, then
  **definitional replacement fails** — evaluating a value no longer yields
  that value (`positional_breaks_definitional_replacement`).

There is no third option, so no semantics gives the symbol both readings.

The conclusion is about *data*, and is exactly this: **zero has no datum
spelling**.  It is not a claim that zero has no syntax.  An explicit
computation form is entirely coherent — this very module uses one, `Expr.zero`
— and a source spelling such as `(empty)` is fine provided it elaborates to
that form rather than to a returned datum.  What the dichotomy forbids is a
single ordinary value that also means zero.

The supporting fact for that last clause is `no_continuation_reports_absence`:
because zero annihilates sequencing, no continuation whatsoever can turn "no
answers" into an answer.  Observing absence therefore cannot be done from
inside the computation; it requires an elimination form that reifies the bag.
-/

namespace Mettapedia.Languages.MeTTa.Emptiness

open Mettapedia.GSLT.Core.Separation
open Mettapedia.GSLT.Core.ObservationIndexedPruning
open Mettapedia.Cybernetics

/-! ## The language -/

/-- Ordinary data.  Every constructor here denotes exactly one answer. -/
inductive Datum where
  /-- The unit datum, written `()`. -/
  | unit
  /-- A container with nothing in it. -/
  | nil
  /-- An uninterpreted symbol. -/
  | sym (name : String)
  /-- Structure. -/
  | cons (head tail : Datum)
  /-- A fault occurrence: a broken question, reported as an answer. -/
  | fault (message : String)
deriving DecidableEq, Repr

/-- Expressions.  An expression denotes a bag of answers. -/
inductive Expr where
  /-- One answer. -/
  | pure (datum : Datum)
  /-- No answers.  This is an effect and deliberately has no datum. -/
  | zero
  /-- Superposition of answers. -/
  | plus (left right : Expr)
  /-- A constructor, whose operands are argument positions. -/
  | build (head tail : Expr)
  /-- An evaluation boundary: the position where a result is returned. -/
  | call (inner : Expr)
  /-- Reify the answer bag as a single datum.  The only observer of zero. -/
  | collapse (inner : Expr)
deriving Repr

/-- One-hole contexts, at arbitrary depth. -/
inductive Ctx where
  | hole
  | plusLeft (context : Ctx) (rest : Expr)
  | plusRight (first : Expr) (context : Ctx)
  | buildHead (context : Ctx) (tail : Expr)
  | buildTail (head : Expr) (context : Ctx)
  | inCall (context : Ctx)
  | inCollapse (context : Ctx)
deriving Repr

/-- Fill a context's hole. -/
def plug : Ctx → Expr → Expr
  | .hole, expression => expression
  | .plusLeft context rest, expression => .plus (plug context expression) rest
  | .plusRight first context, expression => .plus first (plug context expression)
  | .buildHead context tail, expression => .build (plug context expression) tail
  | .buildTail head context, expression => .build head (plug context expression)
  | .inCall context, expression => .call (plug context expression)
  | .inCollapse context, expression => .collapse (plug context expression)

/-! ## The answer algebra -/

/-- Reify a bag as one datum. -/
def encode : List Datum → Datum
  | [] => .nil
  | datum :: rest => .cons datum (encode rest)

/-- Pair every head answer with every tail answer. -/
def consBags (heads tails : List Datum) : List Datum :=
  heads.flatMap fun head => tails.map fun tail => Datum.cons head tail

/-- Sequencing on answer bags. -/
def bindBag (bag : List Datum) (continuation : Datum → List Datum) : List Datum :=
  bag.flatMap continuation

/-- **Zero annihilates sequencing.**  Whatever a continuation would do with
each answer, a computation with no answers has none to give it. -/
@[simp] theorem zero_annihilates (continuation : Datum → List Datum) :
    bindBag [] continuation = [] := rfl

/-- **No continuation can report absence.**  Reporting requires producing an
answer, and by annihilation no continuation produces one from zero.  So the
observation of "there were none" cannot be made from inside the computation;
it is not a continuation but a separate elimination form.

This is the negative half of the case for a dedicated reifying observer.  It
does not by itself show that reification is the *only* such form. -/
theorem no_continuation_reports_absence (continuation : Datum → List Datum)
    (report : Datum) : bindBag [] continuation ≠ [report] := by
  simp

/-! ## The recommended semantics

Zero is an effect with no term; every datum is one answer; `call` is the
identity on answers; `collapse` is the only bridge from effect to data. -/

def denoteClean : Expr → List Datum
  | .pure datum => [datum]
  | .zero => []
  | .plus left right => denoteClean left ++ denoteClean right
  | .build head tail => consBags (denoteClean head) (denoteClean tail)
  | .call inner => denoteClean inner
  | .collapse inner => [encode (denoteClean inner)]

/-! ## The five kinds, and their representatives -/

/-- No answers. -/
def zeroOutcomes : Expr := .zero
/-- One answer: the unit datum. -/
def unitDatum : Expr := .pure .unit
/-- One answer: a container with nothing in it. -/
def emptyCollection : Expr := .pure .nil
/-- One answer: an inert atom that happens to be spelled `Empty`. -/
def emptyAtom : Expr := .pure (.sym "Empty")
/-- One answer: a fault. -/
def faultOccurrence : Expr := .pure (.fault "ill-posed")

/-- The observation system of the recommended semantics. -/
def cleanSystem : ObservationSystem where
  Expr := Expr
  Ctx := Ctx
  Obs := List Datum
  plug := plug
  observe := denoteClean

/-- Every kind is separated from every other at the empty context, so all
five need their own spelling.  Recorded as the full lower triangle. -/
theorem kinds_pairwise_separated :
    cleanSystem.Separates .hole zeroOutcomes unitDatum ∧
    cleanSystem.Separates .hole zeroOutcomes emptyCollection ∧
    cleanSystem.Separates .hole zeroOutcomes emptyAtom ∧
    cleanSystem.Separates .hole zeroOutcomes faultOccurrence ∧
    cleanSystem.Separates .hole unitDatum emptyCollection ∧
    cleanSystem.Separates .hole unitDatum emptyAtom ∧
    cleanSystem.Separates .hole unitDatum faultOccurrence ∧
    cleanSystem.Separates .hole emptyCollection emptyAtom ∧
    cleanSystem.Separates .hole emptyCollection faultOccurrence ∧
    cleanSystem.Separates .hole emptyAtom faultOccurrence := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [ObservationSystem.Separates, cleanSystem, plug, denoteClean,
      zeroOutcomes, unitDatum, emptyCollection, emptyAtom, faultOccurrence]

/-- **The zero/one distinction, in its oldest form.**  A bag holding the
empty collection is not the empty bag — the difference between having no
answers and having one answer that happens to be empty. -/
theorem bag_of_empty_ne_empty_bag :
    denoteClean emptyCollection ≠ denoteClean zeroOutcomes := by
  simp [denoteClean, emptyCollection, zeroOutcomes]

/-- **Reification observes absence.**  `collapse` distinguishes zero from
one answer, which no continuation can do. -/
theorem collapse_observes_absence :
    denoteClean (.collapse zeroOutcomes) ≠ denoteClean (.collapse unitDatum) := by
  simp [denoteClean, encode, zeroOutcomes, unitDatum]

/-! ## Receipted pruning by computational zero

A loop watcher may propose dropping a branch, but the proposal is lawful only
when a checker establishes that the branch denotes no answers at the declared
observation.  This is the semantic role of computational zero.  It is not the
ordinary datum spelled `Empty`.
-/

/-- Observe a list of choice branches by concatenating their answer streams. -/
def choiceBranchObserver : Observer (List Expr) (List Datum) where
  observe := fun branches => branches.flatMap denoteClean

/-- Removing one named branch, with exact occurrence accounting. -/
def pruneBranch (before : List Expr) (branch : Expr) (after : List Expr) :
    PruningChange Expr Unit where
  source := before ++ branch :: after
  target := before ++ after
  receipt := ()
  removed := {branch}
  accounting := by
    rw [← Multiset.coe_add before (branch :: after),
      ← Multiset.coe_add before after,
      ← Multiset.cons_coe branch after,
      ← Multiset.singleton_add]
    ac_rfl

/-- Replacing a denotationally zero branch by choice-zero preserves even the
ordered answer stream, hence every coarser postcomposed observation. -/
theorem prune_denotational_zero_lawful
    (before after : List Expr) (branch : Expr)
    (silent : denoteClean branch = []) :
    LawfulAt choiceBranchObserver
      (pruneBranch before branch after).toChange := by
  simp [LawfulAt, choiceBranchObserver, pruneBranch, silent]

/-- The explicit computation form used for `(empty)` is a positive instance:
it contributes no answer and can therefore disappear from a choice. -/
theorem prune_choice_zero_lawful :
    LawfulAt choiceBranchObserver
      (pruneBranch [] zeroOutcomes [unitDatum]).toChange := by
  apply prune_denotational_zero_lawful
  rfl

/-- A syntactic proposal to remove a productive branch is not authority. -/
theorem prune_productive_branch_not_lawful :
    Not (LawfulAt choiceBranchObserver
      (pruneBranch [] unitDatum []).toChange) := by
  simp [LawfulAt, choiceBranchObserver, pruneBranch,
    denoteClean, unitDatum]

def productiveBranchProposal : Proposal Nat Expr Unit where
  toPruningChange := pruneBranch [] unitDatum []
  observedRevision := 7

def productiveBranchSnapshot : Snapshot Nat Expr Unit where
  revision := 7
  live := [unitDatum]
  pruned := 0
  receipts := []

/-- A current watcher proposal still has no exact admission when it would
erase a productive branch.  Currency is necessary, never sufficient. -/
theorem productive_branch_has_no_exact_admission :
    Not (Admission choiceBranchObserver productiveBranchSnapshot
      productiveBranchProposal) := by
  intro admission
  exact prune_productive_branch_not_lawful admission.lawful

def choiceZeroProposal : Proposal Nat Expr Unit where
  toPruningChange := pruneBranch [] zeroOutcomes [unitDatum]
  observedRevision := 7

def choiceZeroSnapshot : Snapshot Nat Expr Unit where
  revision := 7
  live := [zeroOutcomes, unitDatum]
  pruned := 0
  receipts := []

/-- A current checked zero proposal receives admission. -/
def choiceZeroAdmission : Admission choiceBranchObserver
    choiceZeroSnapshot choiceZeroProposal where
  revisionCurrent := rfl
  sourceCurrent := rfl
  lawful := prune_choice_zero_lawful

/-- The admitted transition retains exact occurrence accounting. -/
theorem choiceZero_apply_conserves :
    ((applyProposal choiceBranchObserver choiceZeroSnapshot
        choiceZeroProposal choiceZeroAdmission).live : Multiset Expr) +
      (applyProposal choiceBranchObserver choiceZeroSnapshot
        choiceZeroProposal choiceZeroAdmission).pruned =
    (choiceZeroSnapshot.live : Multiset Expr) +
      choiceZeroSnapshot.pruned :=
  applyProposal_conserves _ _ _ _

def staleChoiceZeroProposal : Proposal Nat Expr Unit :=
  { choiceZeroProposal with observedRevision := 6 }

/-- Even a semantically valid zero certificate cannot be replayed at a stale
revision. -/
theorem stale_choice_zero_has_no_admission :
    Not (Admission choiceBranchObserver choiceZeroSnapshot
      staleChoiceZeroProposal) := by
  apply stale_has_no_admission
  decide

/-! ## Branch one: the reading applied everywhere

The symbol denotes zero wherever it occurs.  Constructors then annihilate on
it automatically, because a constructor ranges over the answers of its
operands and there are none. -/

def denoteUniform : Expr → List Datum
  | .pure (.sym "Empty") => []
  | .pure datum => [datum]
  | .zero => []
  | .plus left right => denoteUniform left ++ denoteUniform right
  | .build head tail => consBags (denoteUniform head) (denoteUniform tail)
  | .call inner => denoteUniform inner
  | .collapse inner => [encode (denoteUniform inner)]

/-- The uniform reading is a fold on answer bags, hence compositional. -/
theorem denoteUniform_compositional (context : Ctx) {left right : Expr}
    (agree : denoteUniform left = denoteUniform right) :
    denoteUniform (plug context left) = denoteUniform (plug context right) := by
  induction context with
  | hole => exact agree
  | plusLeft context rest inductionHypothesis =>
      simp [plug, denoteUniform, inductionHypothesis]
  | plusRight first context inductionHypothesis =>
      simp [plug, denoteUniform, inductionHypothesis]
  | buildHead context tail inductionHypothesis =>
      simp [plug, denoteUniform, inductionHypothesis]
  | buildTail head context inductionHypothesis =>
      simp [plug, denoteUniform, inductionHypothesis]
  | inCall context inductionHypothesis =>
      simp [plug, denoteUniform, inductionHypothesis]
  | inCollapse context inductionHypothesis =>
      simp [plug, denoteUniform, inductionHypothesis]

/-- **The symbol becomes redundant.**  Under the uniform reading no context
whatsoever distinguishes the atom from `zero`: writing `Empty` and writing
nothing are the same program.  The symbol therefore carries no data and could
be deleted from the language without changing any observation. -/
theorem uniform_makes_atom_redundant (context : Ctx) :
    denoteUniform (plug context emptyAtom) =
      denoteUniform (plug context zeroOutcomes) :=
  denoteUniform_compositional context (by simp [denoteUniform, emptyAtom, zeroOutcomes])

/-! ## Branch two: the reading applied only at results

The symbol survives as written data but is filtered where a result is
returned.  This is the positional treatment, and it is what upstream
behaviour measures out to. -/

def dropAtom (bag : List Datum) : List Datum :=
  bag.filter fun datum => !(datum == Datum.sym "Empty")

def denotePositional : Expr → List Datum
  | .pure datum => [datum]
  | .zero => []
  | .plus left right => denotePositional left ++ denotePositional right
  | .build head tail => consBags (denotePositional head) (denotePositional tail)
  | .call inner => dropAtom (denotePositional inner)
  | .collapse inner => [encode (denotePositional inner)]

/-- Evaluating a value yields that value.  This is what makes inlining a
definition safe. -/
def PreservesValues (denotation : Expr → List Datum) : Prop :=
  ∀ datum : Datum, denotation (.call (.pure datum)) = denotation (.pure datum)

theorem clean_preservesValues : PreservesValues denoteClean := by
  intro datum
  simp [denoteClean]

/-- **The positional reading breaks definitional replacement.**  Evaluating
the atom does not yield the atom, so replacing a definition by its body — or
a body by its value — changes what a program means.  Every measured leak of
this family is an instance. -/
theorem positional_breaks_definitional_replacement :
    ¬ PreservesValues denotePositional := by
  intro preserves
  have atomCase := preserves (.sym "Empty")
  simp [denotePositional, dropAtom] at atomCase

/-- The atom survives in argument position while `zero` does not, so the
constructor is an explicit separating context. -/
theorem positional_separates_atom_from_zero :
    denotePositional (plug (.buildHead .hole unitDatum) emptyAtom) ≠
      denotePositional (plug (.buildHead .hole unitDatum) zeroOutcomes) := by
  simp [plug, denotePositional, consBags, emptyAtom, zeroOutcomes, unitDatum]

/-! ## The dichotomy

Collecting the two branches.  A design that wants the symbol to mean zero
must place the reading somewhere, and both placements are refuted: everywhere
makes the symbol unobservable, and only-at-results breaks inlining.  The
surviving design is the one in which zero has no term at all. -/

/-- **No semantics gives the symbol both readings.**  Stated as the
conjunction actually proved: the uniform placement makes the atom
indistinguishable from zero in every context, and the positional placement
fails definitional replacement. -/
theorem empty_atom_dichotomy :
    (∀ context, denoteUniform (plug context emptyAtom) =
        denoteUniform (plug context zeroOutcomes)) ∧
      ¬ PreservesValues denotePositional :=
  ⟨uniform_makes_atom_redundant, positional_breaks_definitional_replacement⟩

/-- Under the recommended semantics the atom is ordinary data, and is
separated from zero by the empty context — no leak to repair. -/
theorem clean_keeps_atom_as_data :
    cleanSystem.Separable emptyAtom zeroOutcomes :=
  ⟨.hole, by simp [ObservationSystem.Separates, cleanSystem, plug, denoteClean,
    emptyAtom, zeroOutcomes]⟩

/-! ## When sharing a name *is* safe

The separation criterion governs notions competing for one position.  Notions
that never occupy the same position are governed by the grammar instead, and
a shared English word costs nothing — an empty space, an empty type and an
empty production may all be called empty.

Modelled here by a two-sorted system whose contexts accept one sort each: no
context accepts both, so no context separates them. -/

/-- Two sorts that never meet: answers, and the types answers might have. -/
inductive Sorted where
  | answer (expression : Expr)
  | type (name : String)
deriving Repr

/-- Contexts that accept one sort each. -/
inductive SortedCtx where
  | onAnswer (context : Ctx)
  | onType

def sortedPlug? : SortedCtx → Sorted → Option Sorted
  | .onAnswer context, .answer expression => some (.answer (plug context expression))
  | .onAnswer _, .type _ => none
  | .onType, .type name => some (.type name)
  | .onType, .answer _ => none

def sortedObserve : Sorted → List Datum
  | .answer expression => denoteClean expression
  | .type name => [.sym name]

def sortedSystem : SortedObservationSystem where
  Expr := Sorted
  Ctx := SortedCtx
  Obs := List Datum
  plug? := sortedPlug?
  observe := sortedObserve

/-- The empty collection, as an answer. -/
def emptyCollectionAnswer : Sorted := .answer emptyCollection
/-- The empty type, as a type. -/
def emptyTypeName : Sorted := .type "Empty"

/-- **A safe shared name.**  No context accepts both an answer and a type, so
none separates them, and calling both of them empty cannot cause a
confusion.  The criterion that refuses the in-band zero permits this. -/
theorem empty_collection_and_empty_type_never_compete (context : SortedCtx) :
    ¬ sortedSystem.Separates context emptyCollectionAnswer emptyTypeName := by
  apply SortedObservationSystem.not_separates_of_no_common_context
  rintro (inner | _) ⟨accepted, rejected⟩ <;>
    simp [SortedObservationSystem.Accepts, sortedSystem, sortedPlug?,
      emptyCollectionAnswer, emptyTypeName] at accepted rejected

end Mettapedia.Languages.MeTTa.Emptiness

#print axioms Mettapedia.Languages.MeTTa.Emptiness.prune_choice_zero_lawful
#print axioms Mettapedia.Languages.MeTTa.Emptiness.prune_productive_branch_not_lawful
#print axioms Mettapedia.Languages.MeTTa.Emptiness.productive_branch_has_no_exact_admission
#print axioms Mettapedia.Languages.MeTTa.Emptiness.choiceZero_apply_conserves
#print axioms Mettapedia.Languages.MeTTa.Emptiness.stale_choice_zero_has_no_admission
