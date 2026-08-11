import Mettapedia.GSLT.LanguageDef.ContextSupport
import Mettapedia.GSLT.Dynamics.CollapseAlgebra
import Mettapedia.Languages.MeTTa.EmptinessTaxonomy
import Mettapedia.Languages.MeTTa.MeTTaZero

/-!
# Revision-threaded query, bind, evaluation, and publication

This module isolates four MeTTa roles without choosing a scheduler or a
physical space representation.

* `Match` reads one named space revision and retains atom and matcher
  occurrence evidence.
* `Let` composes arbitrary proof-relevant computations while threading the
  resulting world.
* `Eval` is a supplied activation computation; it is not identified with
  normalization.
* `Emit` is the generic production operation.  This module's persistent-space
  emitter publishes one occurrence and advances the world revision;
  `AddAtom` is its MeTTa compatibility spelling.

The computation carrier is relational and proof relevant.  A backend may use
mutable C storage or persistent PathMap storage, but both must refine the same
before/after world relation.

The final section records the binding boundary required by an ABT lowering.
Depth-blind free-variable substitution is adequate for closed top-level
answers, but it is not adequate when a matched value crosses binders.  The
existing support-indexed locally nameless substitution performs the required
de Bruijn weakening.
-/

namespace Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval

open Mettapedia.Languages.MeTTa.MeTTaZero
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.GSLT.LanguageDef

universe uWorld uValue uMiddle uResult uEvidence uSpace

/-! ## A proof-relevant state-and-answer computation -/

/-- A computation relates an input world, an output world, and one answer.
Different inhabitants retain different answer occurrences or execution
receipts even when their endpoints coincide. -/
abbrev Computation (World : Type uWorld) (Answer : Type uValue) :=
  World → World → Answer → Type uEvidence

/-- Pure production changes no world. -/
inductive Pure {World : Type uWorld} {Answer : Type uValue}
    (value : Answer) : Computation World Answer where
  | return (world : World) : Pure value world world value

/-- Proof-relevant Kleisli composition.  Both the intermediate world and the
exact intermediate answer remain part of the evidence. -/
def Bind {World : Type uWorld} {A : Type uValue} {B : Type uResult}
    (producer : Computation World A)
    (continuation : A → Computation World B) : Computation World B :=
  fun before after result =>
    Σ middle, Σ value, producer before middle value ×
      continuation value middle after result

/-- Composition is associative by reassociating evidence, without erasing
either intermediate world or answer. -/
def bindAssoc {World : Type uWorld} {A : Type uValue}
    {B : Type uMiddle} {C : Type uResult}
    (first : Computation World A)
    (second : A → Computation World B)
    (third : B → Computation World C)
    (before after : World) (result : C) :
    Bind (Bind first second) third before after result ≃
      Bind first (fun value => Bind (second value) third) before after result where
  toFun
    | ⟨secondWorld, secondValue,
        ⟨firstWorld, firstValue, firstEvidence, secondEvidence⟩,
        thirdEvidence⟩ =>
      ⟨firstWorld, firstValue, firstEvidence,
        ⟨secondWorld, secondValue, secondEvidence, thirdEvidence⟩⟩
  invFun
    | ⟨firstWorld, firstValue, firstEvidence,
        ⟨secondWorld, secondValue, secondEvidence, thirdEvidence⟩⟩ =>
      ⟨secondWorld, secondValue,
        ⟨firstWorld, firstValue, firstEvidence, secondEvidence⟩,
        thirdEvidence⟩
  left_inv := by
    intro evidence
    obtain ⟨_, _, ⟨_, _, _, _⟩, _⟩ := evidence
    rfl
  right_inv := by
    intro evidence
    obtain ⟨_, _, _, ⟨_, _, _, _⟩⟩ := evidence
    rfl

/-- `Eval` names activation only.  Whether an activation is one step,
normalizing, bounded, or demand driven belongs to the supplied profile. -/
abbrev Eval {World : Type uWorld}
    (activate : Pattern → Computation World Pattern)
    (subject : Pattern) : Computation World Pattern :=
  activate subject

/-! ## Generic emission -/

/-- An emitter interprets a target and payload as a proof-relevant state
transition.  Different profiles may install persistent-space, linear-channel,
work-queue, or external-capability emitters without changing `Bind`. -/
abbrev Emitter (World : Type uWorld) (Target : Type uSpace)
    (Payload : Type uValue) :=
  Target → Payload → Computation World Unit

/-- Produce one payload through the selected emitter.  The result is unit;
the emission receipt remains in the proof-relevant computation evidence. -/
abbrev Emit {World : Type uWorld} {Target : Type uSpace}
    {Payload : Type uValue} (emitter : Emitter World Target Payload)
    (target : Target) (payload : Payload) : Computation World Unit :=
  emitter target payload

/-! ## Revisioned named spaces -/

/-- A finite-occurrence world with an explicit monotone revision number.
Names select spaces; each space is an occurrence multiset rather than a set. -/
structure RevisionedSpaces (SpaceName : Type uSpace) where
  revision : Nat
  contents : SpaceName → Multiset Pattern

/-- Publish one new occurrence in a named space and advance the revision. -/
def addAtomWorld {SpaceName : Type uSpace} [DecidableEq SpaceName]
    (world : RevisionedSpaces SpaceName) (space : SpaceName)
    (atom : Pattern) : RevisionedSpaces SpaceName where
  revision := world.revision + 1
  contents := fun candidate =>
    if candidate = space then atom ::ₘ world.contents candidate
    else world.contents candidate

/-- The receipt for one publication.  It identifies both endpoint revisions
and the exact published occurrence. -/
structure PersistentEmitReceipt {SpaceName : Type uSpace} [DecidableEq SpaceName]
    (before after : RevisionedSpaces SpaceName)
    (space : SpaceName) (atom : Pattern) : Type where
  after_eq : after = addAtomWorld before space atom

/-- The persistent-space interpretation of `emit`. -/
def persistentSpaceEmitter {SpaceName : Type uSpace} [DecidableEq SpaceName] :
    Emitter (RevisionedSpaces SpaceName) SpaceName Pattern :=
  fun space atom before after result =>
    PersistentEmitReceipt before after space atom × PLift (result = ())

/-- MeTTa's `add-atom` is the compatibility spelling for persistent emission
into a named space. -/
abbrev AddAtom {SpaceName : Type uSpace} [DecidableEq SpaceName]
    (space : SpaceName) (atom : Pattern) :
    Computation (RevisionedSpaces SpaceName) Unit :=
  Emit persistentSpaceEmitter space atom

/-- The two spellings have definitionally identical semantics. -/
theorem addAtom_eq_emit {SpaceName : Type uSpace} [DecidableEq SpaceName]
    (space : SpaceName) (atom : Pattern) :
    AddAtom space atom = Emit persistentSpaceEmitter space atom :=
  rfl

/-- Expanded persistent-emission relation, useful to physical refinements. -/
theorem persistentSpaceEmitter_apply
    {SpaceName : Type uSpace} [DecidableEq SpaceName]
    (space : SpaceName) (atom : Pattern)
    (before after : RevisionedSpaces SpaceName) (result : Unit) :
    Emit persistentSpaceEmitter space atom before after result =
      (PersistentEmitReceipt before after space atom × PLift (result = ())) :=
  rfl

@[simp] theorem addAtomWorld_revision
    {SpaceName : Type uSpace} [DecidableEq SpaceName]
    (world : RevisionedSpaces SpaceName) (space : SpaceName)
    (atom : Pattern) :
    (addAtomWorld world space atom).revision = world.revision + 1 :=
  rfl

@[simp] theorem addAtomWorld_contents_same
    {SpaceName : Type uSpace} [DecidableEq SpaceName]
    (world : RevisionedSpaces SpaceName) (space : SpaceName)
    (atom : Pattern) :
    (addAtomWorld world space atom).contents space =
      atom ::ₘ world.contents space := by
  simp [addAtomWorld]

@[simp] theorem addAtomWorld_contents_other
    {SpaceName : Type uSpace} [DecidableEq SpaceName]
    (world : RevisionedSpaces SpaceName) {written read : SpaceName}
    (different : read ≠ written) (atom : Pattern) :
    (addAtomWorld world written atom).contents read = world.contents read := by
  simp [addAtomWorld, different]

@[simp] theorem addAtomWorld_count_same
    {SpaceName : Type uSpace} [DecidableEq SpaceName]
    (world : RevisionedSpaces SpaceName) (space : SpaceName)
    (atom : Pattern) :
    Multiset.count atom ((addAtomWorld world space atom).contents space) =
      Multiset.count atom (world.contents space) + 1 := by
  simp [Nat.add_comm]

/-! ## Occurrence-preserving named-space matching -/

/-- One exact answer occurrence of a named-space query.  Atom multiplicity,
matcher multiplicity, and checked continuation instantiation are independent
coordinates. -/
structure MatchEvent (model : Model)
    {SpaceName : Type uSpace} (world : RevisionedSpaces SpaceName)
    (space : SpaceName) (pattern template result : Pattern) where
  candidate : Pattern
  atomOccurrence : Nat
  atomOccurrence_exists :
    atomOccurrence < Multiset.count candidate (world.contents space)
  bindings : Bindings
  matchOccurrence : Nat
  matchOccurrence_exists :
    matchOccurrence < Multiset.count bindings
      (model.matchAtoms pattern candidate)
  instantiates : applyBindingsGround? bindings template = some result

/-- A named-space match is read-only at the world level. -/
structure MatchArticle (model : Model)
    {SpaceName : Type uSpace}
    (space : SpaceName) (pattern template : Pattern)
    (before after : RevisionedSpaces SpaceName) (result : Pattern) where
  readOnly : after = before
  event : MatchEvent model before space pattern template result

/-- `match` is the read-only computation generated by occurrence-aware space
matching and checked template instantiation. -/
def Match (model : Model) {SpaceName : Type uSpace}
    (space : SpaceName) (pattern template : Pattern) :
    Computation (RevisionedSpaces SpaceName) Pattern :=
  MatchArticle model space pattern template

/-! ## Semantically subordinate candidate selection -/

/-- The part of a match event that a physical index may select before the
authored matcher checks bindings and continuation instantiation. -/
structure CandidateOccurrence
    {SpaceName : Type uSpace} (world : RevisionedSpaces SpaceName)
    (space : SpaceName) where
  candidate : Pattern
  atomOccurrence : Nat
  atomOccurrence_exists :
    atomOccurrence < Multiset.count candidate (world.contents space)

/-- A physical candidate selector may retain arbitrary proof-relevant index or
backend evidence.  It does not itself establish that the candidate matches. -/
abbrev CandidateSelector
    {SpaceName : Type uSpace} (world : RevisionedSpaces SpaceName)
    (space : SpaceName) := CandidateOccurrence world space → Type uEvidence

/-- Completeness is the sole semantic obligation required of a candidate
selector: every concrete authored matcher occurrence must be selectable.
False positives remain safe because the authored matcher is rerun below. -/
def CandidateComplete (model : Model)
    {SpaceName : Type uSpace} {world : RevisionedSpaces SpaceName}
    {space : SpaceName} {pattern : Pattern}
    (selector : CandidateSelector world space) :=
  ∀ (candidate : CandidateOccurrence world space)
    (bindings : Bindings) (matchOccurrence : Nat),
    matchOccurrence < Multiset.count bindings
      (model.matchAtoms pattern candidate.candidate) →
    selector candidate

/-- Match execution factored through an untrusted candidate selector.  The
selected row is followed by the same authored matcher occurrence and checked
template instantiation carried by `MatchEvent`. -/
structure MatchViaCandidate (model : Model)
    {SpaceName : Type uSpace}
    (space : SpaceName) (pattern template : Pattern)
    (before after : RevisionedSpaces SpaceName) (result : Pattern)
    (selector : CandidateSelector before space) where
  readOnly : after = before
  candidate : CandidateOccurrence before space
  selected : selector candidate
  bindings : Bindings
  matchOccurrence : Nat
  matchOccurrence_exists :
    matchOccurrence < Multiset.count bindings
      (model.matchAtoms pattern candidate.candidate)
  instantiates : applyBindingsGround? bindings template = some result

/-- A complete physical selector can realize every direct match article. -/
def matchArticleToCandidate (model : Model)
    {SpaceName : Type uSpace}
    {space : SpaceName} {pattern template result : Pattern}
    {before after : RevisionedSpaces SpaceName}
    {selector : CandidateSelector before space}
    (complete : CandidateComplete model (pattern := pattern) selector) :
    MatchArticle model space pattern template before after result →
      MatchViaCandidate model space pattern template
        before after result selector
  | article => {
      readOnly := article.readOnly
      candidate := {
        candidate := article.event.candidate
        atomOccurrence := article.event.atomOccurrence
        atomOccurrence_exists := article.event.atomOccurrence_exists }
      selected := complete
        { candidate := article.event.candidate
          atomOccurrence := article.event.atomOccurrence
          atomOccurrence_exists := article.event.atomOccurrence_exists }
        article.event.bindings article.event.matchOccurrence
        article.event.matchOccurrence_exists
      bindings := article.event.bindings
      matchOccurrence := article.event.matchOccurrence
      matchOccurrence_exists := article.event.matchOccurrence_exists
      instantiates := article.event.instantiates }

/-- Candidate selection cannot invent an authored match: erasing its physical
evidence reconstructs an ordinary `MatchArticle` without assumptions. -/
def candidateToMatchArticle (model : Model)
    {SpaceName : Type uSpace}
    {space : SpaceName} {pattern template result : Pattern}
    {before after : RevisionedSpaces SpaceName}
    {selector : CandidateSelector before space} :
    MatchViaCandidate model space pattern template
        before after result selector →
      MatchArticle model space pattern template before after result
  | article => {
      readOnly := article.readOnly
      event := {
        candidate := article.candidate.candidate
        atomOccurrence := article.candidate.atomOccurrence
        atomOccurrence_exists := article.candidate.atomOccurrence_exists
        bindings := article.bindings
        matchOccurrence := article.matchOccurrence
        matchOccurrence_exists := article.matchOccurrence_exists
        instantiates := article.instantiates } }

/-- Candidate pushdown preserves exactly the existence of match answers when
the selector is complete.  Soundness of the selector is deliberately absent:
the authored matcher makes false positives observationally irrelevant. -/
theorem match_nonempty_iff_candidate_nonempty (model : Model)
    {SpaceName : Type uSpace}
    {space : SpaceName} {pattern template result : Pattern}
    {before after : RevisionedSpaces SpaceName}
    {selector : CandidateSelector before space}
    (complete : CandidateComplete model (pattern := pattern) selector) :
    Nonempty (MatchArticle model space pattern template before after result) ↔
      Nonempty (MatchViaCandidate model space pattern template
        before after result selector) := by
  constructor
  · rintro ⟨article⟩
    exact ⟨matchArticleToCandidate model complete article⟩
  · rintro ⟨article⟩
    exact ⟨candidateToMatchArticle model article⟩

/-! ## Patterned computation bind -/

/-- One checked occurrence of binding a producer answer to a continuation
pattern.  Ground checked application is the conservative executable fragment;
the support-indexed ABT generalization is isolated below. -/
structure LetBinding (model : Model)
    (pattern body value instantiated : Pattern) where
  bindings : Bindings
  occurrence : Nat
  occurrence_exists :
    occurrence < Multiset.count bindings (model.matchAtoms pattern value)
  instantiates : applyBindingsGround? bindings body = some instantiated

/-- Patterned `let` is ordinary proof-relevant stateful bind, followed by one
checked pattern occurrence and activation of the instantiated continuation. -/
def Let {World : Type uWorld} (model : Model)
    (activate : Pattern → Computation World Pattern)
    (pattern : Pattern) (producer : Computation World Pattern)
    (body : Pattern) : Computation World Pattern :=
  Bind producer fun value before after result =>
    Σ instantiated, LetBinding model pattern body value instantiated ×
      Eval activate instantiated before after result

/-! ## Why reification is a handler rather than another bind

`Bind` can use each answer a producer emits, but it has no branch to run when
the producer emits no answer.  Reifying the completed answer family therefore
requires an elimination form outside Kleisli composition.  A collapse algebra
is that elimination form; its `zero` and `finish` fields specify what a
completed empty frontier means.

This is also the fail-closed boundary for physical implementations.  A backend
may invoke a collapse handler only after supplying completeness evidence for
the frontier it presents.  A partial search must instead retain residual work.
-/

namespace ObservationBoundary

open Mettapedia.GSLT.Dynamics.Collapse
open Mettapedia.Languages.MeTTa.Emptiness

/-- If the producer has no event from the input world, patterned or ordinary
bind cannot manufacture a result through its continuation. -/
theorem no_bind_answer_of_no_producer_answer
    {World : Type uWorld} {A : Type uValue} {B : Type uResult}
    (producer : Computation World A)
    (continuation : A → Computation World B)
    (before after : World) (result : B)
    (producerEmpty : ∀ middle value, ¬ Nonempty (producer before middle value)) :
    ¬ Nonempty (Bind producer continuation before after result) := by
  rintro ⟨middle, value, producerEvidence, _⟩
  exact producerEmpty middle value ⟨producerEvidence⟩

/-- The empty completed answer family can be reified by a collapse handler,
but by `no_continuation_reports_absence` no continuation can produce that
report from the empty computation. -/
theorem reified_empty_is_not_bind_derived :
    ¬ ∃ continuation : Datum → List Datum,
      bindBag [] continuation = [encode []] := by
  rintro ⟨continuation, reports⟩
  exact no_continuation_reports_absence continuation (encode []) reports

/-- A collapse algebra sees a completed empty frontier through its explicit
`zero` and `finish`; this is the positive operation missing from bind. -/
theorem collapse_completed_empty {O R Result : Type}
    (algebra : CollapseAlgebra O R Result) :
    collapseWith algebra [] = algebra.finish algebra.zero :=
  rfl

/-- The standard occurrence-preserving collector retains both copies of an
equal answer.  Reification therefore need not quotient the answer effect. -/
theorem collect_preserves_duplicate_occurrences
    {Answer Receipt : Type} (answer : Answer) (receipt : Receipt) :
    collapseWith (Collect Answer Receipt)
        [⟨answer, 1, receipt⟩, ⟨answer, 1, receipt⟩] = [answer, answer] := by
  rfl

end ObservationBoundary

/-! ## Publication/query canaries -/

namespace Canary

def fact : Pattern := .apply "V" []
def anyPattern : Pattern := .fvar "x"
def anyTemplate : Pattern := .fvar "x"

def emptyWorld : RevisionedSpaces Bool where
  revision := 0
  contents := fun _ => 0

def worldAfterAdd : RevisionedSpaces Bool :=
  addAtomWorld emptyWorld false fact

def addFact : AddAtom false fact emptyWorld worldAfterAdd () :=
  ⟨⟨rfl⟩, ⟨rfl⟩⟩

def matchFactAfterAdd :
    Match (structuralModel fun _ => 0) false anyPattern anyTemplate
      worldAfterAdd worldAfterAdd fact where
  readOnly := rfl
  event := {
    candidate := fact
    atomOccurrence := 0
    atomOccurrence_exists := by simp [worldAfterAdd, emptyWorld]
    bindings := [("x", fact)]
    matchOccurrence := 0
    matchOccurrence_exists := by
      simp [structuralModel, fact, anyPattern, matchPattern]
    instantiates := by
      exact applyBindingsGround?_accepts_ground_binding_value }

/-- Positive selector canary: returning every physical row is complete even
though it may be inefficient, because authored matching remains downstream. -/
def selectAllCandidates : CandidateSelector worldAfterAdd false :=
  fun _ => Unit

def selectAllCandidates_complete : CandidateComplete
    (structuralModel fun _ => 0) (pattern := anyPattern)
    selectAllCandidates :=
  fun _ _ _ _ => ()

/-- Negative selector canary: dropping every row violates completeness for the
known matching occurrence. -/
def selectNoCandidates : CandidateSelector worldAfterAdd false :=
  fun _ => Empty

theorem selectNoCandidates_incomplete :
    ¬ Nonempty (CandidateComplete
      (structuralModel fun _ => 0) (pattern := anyPattern)
      selectNoCandidates) := by
  rintro ⟨complete⟩
  let candidate : CandidateOccurrence worldAfterAdd false := {
    candidate := matchFactAfterAdd.event.candidate
    atomOccurrence := matchFactAfterAdd.event.atomOccurrence
    atomOccurrence_exists := matchFactAfterAdd.event.atomOccurrence_exists }
  have impossible : Empty := complete
    candidate matchFactAfterAdd.event.bindings
    matchFactAfterAdd.event.matchOccurrence
    matchFactAfterAdd.event.matchOccurrence_exists
  exact nomatch impossible

/-- Positive: an authored computation can publish an occurrence and then read
that exact successor revision through ordinary bind. -/
def addThenMatch :
    Bind (AddAtom false fact)
      (fun _ => Match (structuralModel fun _ => 0) false anyPattern anyTemplate)
      emptyWorld worldAfterAdd fact :=
  ⟨worldAfterAdd, (), addFact, matchFactAfterAdd⟩

/-- Negative: the query cannot observe the future occurrence before the
publication event. -/
theorem no_match_before_add :
    ¬ Nonempty (Match (structuralModel fun _ => 0) false anyPattern anyTemplate
      emptyWorld emptyWorld fact) := by
  rintro ⟨article⟩
  have impossible := article.event.atomOccurrence_exists
  simp [emptyWorld] at impossible

/-- Negative: publication in one named space changes neither the contents nor
the query profile of a distinct space. -/
theorem add_does_not_leak_to_other_space :
    (addAtomWorld emptyWorld false fact).contents true = 0 := by
  simp [emptyWorld, addAtomWorld]

end Canary

/-! ## ABT/de Bruijn binding boundary -/

namespace ABTBoundary

def valueType : TypeExpr := .base "Value"

/-- The matched value depends on one surrounding binder. -/
def oneBinderSupport : ContextSupport.Support :=
  fun name => if name = "x" then [valueType] else []

def boundAssignment : ContextSupport.Assignment :=
  fun name => if name = "x" then .bvar 0 else .fvar name

def deeperUse : Pattern :=
  .lambda none (.lambda none (.fvar "x"))

/-- The current depth-blind matcher inserts `#0` under two binders.  This is
the capture-prone result and therefore cannot authorize the general ABT lane. -/
theorem depthBlind_result :
    applyBindings? [("x", .bvar 0)] deeperUse =
      some (.lambda none (.lambda none (.bvar 0))) := by
  exact applyBindings?_binder_depth_counterexample.2.1

/-- Support-indexed substitution remembers that the value originated under
one binder and weakens it to `#1` when used under two. -/
theorem supportIndexed_result :
    ContextSupport.substituteAt oneBinderSupport boundAssignment 0 deeperUse =
      .lambda none (.lambda none (.bvar 1)) := by
  simp [ContextSupport.substituteAt, oneBinderSupport, boundAssignment,
    deeperUse, valueType, liftBVars]

/-- The two results are observably different canonical ABTs. -/
theorem depthBlind_is_not_supportIndexed :
    applyBindings? [("x", .bvar 0)] deeperUse ≠
      some (ContextSupport.substituteAt
        oneBinderSupport boundAssignment 0 deeperUse) := by
  rw [depthBlind_result, supportIndexed_result]
  decide

end ABTBoundary

end Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval
