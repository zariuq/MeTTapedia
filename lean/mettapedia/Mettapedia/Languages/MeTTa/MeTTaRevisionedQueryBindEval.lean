import Mettapedia.Languages.MeTTa.PeTTa.Eval
import Mettapedia.Languages.MeTTa.OSLFCore.Bridge
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics
import Mettapedia.Languages.ProcessCalculi.MORK.MatchSpec
import Mettapedia.Languages.MeTTa.PeTTa.ProfileBridge
import Mettapedia.OSLF.MeTTaIL.GeneralRuleJobs
import Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation
import Mathlib.Data.Multiset.Filter
import Mettapedia.GSLT.LanguageDef.ContextSupport
import Mettapedia.GSLT.Dynamics.CollapseAlgebra
import Mettapedia.Languages.FiniteChoice.EmptinessTaxonomy
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

/-! ## Complete exact frontiers and existence-only observation

Candidate completeness alone licenses pruning before the authored matcher,
but it does not license replacing matching by structural membership.  The
additional exact-frontier certificate below says precisely when that stronger
replacement is valid.  Template totality is separate again: a matching row
need not emit an answer when checked template application can fail.

These distinctions are the semantic boundary used by a runtime which lowers
`collapse (once (match ...))` to an existence query.  The optimization does
not reconstruct answers; it computes only the strictly coarser `AnyAlg`
observation of a completed frontier.
-/

namespace ExistenceObserver

open Mettapedia.GSLT.Dynamics.Collapse

/-- Existence of at least one authored matcher occurrence, before applying a
match template. -/
def HasMatch (model : Model)
    {SpaceName : Type uSpace} (world : RevisionedSpaces SpaceName)
    (space : SpaceName) (pattern : Pattern) : Prop :=
  ∃ candidate : CandidateOccurrence world space,
    ∃ bindings : Bindings, ∃ occurrence : Nat,
      occurrence < Multiset.count bindings
        (model.matchAtoms pattern candidate.candidate)

/-- A selected frontier is exact for one pattern when, on every selected
occurrence, authored matching is equivalent to structural equality with that
pattern.  This is stronger than candidate completeness and is intentionally
sold separately. -/
def CandidateExact (model : Model)
    {SpaceName : Type uSpace} {world : RevisionedSpaces SpaceName}
    {space : SpaceName} {pattern : Pattern}
    (selector : CandidateSelector world space) : Prop :=
  ∀ (candidate : CandidateOccurrence world space)
    (_selected : selector candidate),
    (∃ bindings : Bindings, ∃ occurrence : Nat,
      occurrence < Multiset.count bindings
        (model.matchAtoms pattern candidate.candidate)) ↔
      candidate.candidate = pattern

/-- The physical existence fact exposed by an exact candidate frontier. -/
def FrontierContainsPattern
    {SpaceName : Type uSpace} {world : RevisionedSpaces SpaceName}
    {space : SpaceName} (pattern : Pattern)
    (selector : CandidateSelector world space) : Prop :=
  ∃ candidate : CandidateOccurrence world space,
    Nonempty (selector candidate) ∧ candidate.candidate = pattern

/-- Completeness supplies every true matcher occurrence; exactness turns the
selected matcher question into structural membership.  Together they make
frontier membership an exact existence observer. -/
theorem hasMatch_iff_frontierContainsPattern (model : Model)
    {SpaceName : Type uSpace} {world : RevisionedSpaces SpaceName}
    {space : SpaceName} {pattern : Pattern}
    {selector : CandidateSelector world space}
    (complete : CandidateComplete model (pattern := pattern) selector)
    (exact : CandidateExact model (pattern := pattern) selector) :
    HasMatch model world space pattern ↔
      FrontierContainsPattern pattern selector := by
  constructor
  · rintro ⟨candidate, bindings, occurrence, matched⟩
    let selected := complete candidate bindings occurrence matched
    exact ⟨candidate, ⟨selected⟩,
      (exact candidate selected).mp ⟨bindings, occurrence, matched⟩⟩
  · rintro ⟨candidate, ⟨selected⟩, equal⟩
    obtain ⟨bindings, occurrence, matched⟩ :=
      (exact candidate selected).mpr equal
    exact ⟨candidate, bindings, occurrence, matched⟩

/-- Existence of at least one visible result after checked template
application. -/
def HasMatchAnswer (model : Model)
    {SpaceName : Type uSpace} (world : RevisionedSpaces SpaceName)
    (space : SpaceName) (pattern template : Pattern) : Prop :=
  ∃ result, Nonempty
    (MatchArticle model space pattern template world world result)

/-- Every authored matcher occurrence accepted by the frontier produces one
checked template result.  A translation-time value certificate may establish
this property; a computed, empty, or unresolved template may not. -/
def TemplateTotalOnMatches (model : Model)
    {SpaceName : Type uSpace} (world : RevisionedSpaces SpaceName)
    (space : SpaceName) (pattern template : Pattern) : Prop :=
  ∀ (candidate : CandidateOccurrence world space)
    (bindings : Bindings) (occurrence : Nat),
    occurrence < Multiset.count bindings
      (model.matchAtoms pattern candidate.candidate) →
    ∃ result, applyBindingsGround? bindings template = some result

/-- Template totality is exactly the missing direction from matcher existence
to visible-answer existence. -/
theorem hasMatchAnswer_iff_hasMatch (model : Model)
    {SpaceName : Type uSpace} {world : RevisionedSpaces SpaceName}
    {space : SpaceName} {pattern template : Pattern}
    (total : TemplateTotalOnMatches model world space pattern template) :
    HasMatchAnswer model world space pattern template ↔
      HasMatch model world space pattern := by
  constructor
  · rintro ⟨result, ⟨article⟩⟩
    exact ⟨{
      candidate := article.event.candidate
      atomOccurrence := article.event.atomOccurrence
      atomOccurrence_exists := article.event.atomOccurrence_exists },
      article.event.bindings, article.event.matchOccurrence,
      article.event.matchOccurrence_exists⟩
  · rintro ⟨candidate, bindings, occurrence, matched⟩
    obtain ⟨result, instantiated⟩ :=
      total candidate bindings occurrence matched
    exact ⟨result, ⟨{
      readOnly := rfl
      event := {
        candidate := candidate.candidate
        atomOccurrence := candidate.atomOccurrence
        atomOccurrence_exists := candidate.atomOccurrence_exists
        bindings := bindings
        matchOccurrence := occurrence
        matchOccurrence_exists := matched
        instantiates := instantiated } }⟩⟩

/-- The complete zero-observer law used by exact match-existence fusion.
Absence may be concluded only after candidate completeness, selected-frontier
exactness, and template totality have all been supplied. -/
theorem noMatchAnswer_iff_frontierAbsent (model : Model)
    {SpaceName : Type uSpace} {world : RevisionedSpaces SpaceName}
    {space : SpaceName} {pattern template : Pattern}
    {selector : CandidateSelector world space}
    (complete : CandidateComplete model (pattern := pattern) selector)
    (exact : CandidateExact model (pattern := pattern) selector)
    (total : TemplateTotalOnMatches model world space pattern template) :
    (¬ HasMatchAnswer model world space pattern template) ↔
      (¬ FrontierContainsPattern pattern selector) := by
  rw [hasMatchAnswer_iff_hasMatch model total,
    hasMatch_iff_frontierContainsPattern model complete exact]

/-- A list-level model of committed first-answer observation. -/
def onceList {Answer : Type} : List Answer → List Answer
  | [] => []
  | answer :: _ => [answer]

/-- `once` preserves precisely whether the completed answer stream is empty. -/
theorem onceList_eq_nil_iff {Answer : Type} (answers : List Answer) :
    onceList answers = [] ↔ answers = [] := by
  cases answers <;> simp [onceList]

/-- Unit-multiplicity observations are the occurrence stream emitted by an
ordinary match enumerator. -/
def unitObservations {Answer Receipt : Type}
    (receipt : Receipt) (answers : List Answer) : List (Obs Answer Receipt) :=
  answers.map fun answer => ⟨answer, 1, receipt⟩

/-- `AnyAlg` returns false on a unit-occurrence stream exactly when the stream
is empty. -/
theorem anyUnit_eq_false_iff {Answer Receipt : Type}
    (receipt : Receipt) (answers : List Answer) :
    collapseWith (AnyAlg Answer Receipt) (unitObservations receipt answers) =
        false ↔
      answers = [] := by
  cases answers <;> simp [unitObservations, collapseWith, foldStream, AnyAlg]

/-- Reifying the committed first answer and comparing it with the empty list
is exactly the `AnyAlg` observation of the complete stream.  The right side
neither constructs nor determines the discarded answer values. -/
theorem collectOnce_empty_iff_anyFalse {Answer Receipt : Type}
    (receipt : Receipt) (answers : List Answer) :
    collapseWith (Collect Answer Receipt)
          (unitObservations receipt (onceList answers)) = [] ↔
      collapseWith (AnyAlg Answer Receipt)
          (unitObservations receipt answers) = false := by
  have collectOnce :
      collapseWith (Collect Answer Receipt)
          (unitObservations receipt (onceList answers)) = onceList answers := by
    simpa [unitObservations] using
      (collect_is_legacy_collapse (Receipt := Receipt)
        (onceList answers) receipt)
  rw [collectOnce, anyUnit_eq_false_iff]
  exact onceList_eq_nil_iff answers

end ExistenceObserver

/-! ## Patterned computation bind -/

/- Every free-variable occurrence has enough surrounding binders for the
support declared for that variable. This guard reads occurrence depth, not
merely the set of names in the whole pattern. -/
mutual

def supportsAvailableAt (support : ContextSupport.Support) (depth : Nat) :
    Pattern → Bool
  | .bvar _ => true
  | .fvar name => decide ((support name).length ≤ depth)
  | .apply _ arguments => supportsAvailableIn support depth arguments
  | .lambda _ body => supportsAvailableAt support (depth + 1) body
  | .multiLambda arity _ body => supportsAvailableAt support (depth + arity) body
  | .subst body replacement =>
      supportsAvailableAt support (depth + 1) body &&
      supportsAvailableAt support depth replacement
  | .collection _ elements _ => supportsAvailableIn support depth elements
termination_by pattern => sizeOf pattern

def supportsAvailableIn (support : ContextSupport.Support) (depth : Nat) :
    List Pattern → Bool
  | [] => true
  | first :: rest => supportsAvailableAt support depth first && supportsAvailableIn support depth rest
termination_by patterns => sizeOf patterns

end



/-- Read one matcher assignment without applying it beneath object binders.
The separate support action performs all context transport. -/
def bindingAssignment (bindings : Bindings) : ContextSupport.Assignment :=
  fun name => (bindings.lookup name).getD (.fvar name)

/-- One occurrence of contextual pattern binding.  The capture support is
checked against the actual source pattern; every assigned value is scoped at
that support.  All repeated occurrences in the source pattern must agree on
their capture depth.  The instantiated body uses the independently defined
support action, retaining explicit substitution and collection-rest syntax. -/
structure SupportedLetBinding (model : Model)
    (support : ContextSupport.Support) (depth : Nat)
    (pattern body value instantiated : Pattern) where
  bindings : Bindings
  occurrence : Nat
  occurrence_exists :
    occurrence < Multiset.count bindings (model.matchAtoms pattern value)
  unique : bindings.hasUniqueNames = true
  capturesAligned : depthAligned pattern 0 pattern = true
  captured : ∀ entry ∈ bindings,
    captureDepth entry.1 depth pattern = some (support entry.1).length ∧
      entry.2.isWellScopedAt (support entry.1).length = true
  available : supportsAvailableAt support depth body = true
  instantiates : ContextSupport.substituteAt support
    (bindingAssignment bindings) depth body = instantiated

/-- Contextual named-space matching retains the source occurrence and the
support-aware matching receipt separately. -/
structure SupportedMatchArticle (model : Model)
    {SpaceName : Type uSpace}
    (space : SpaceName) (pattern template : Pattern)
    (support : ContextSupport.Support) (depth : Nat)
    (before after : RevisionedSpaces SpaceName) (result : Pattern) where
  readOnly : after = before
  candidate : CandidateOccurrence before space
  binding : SupportedLetBinding model support depth
    pattern template candidate.candidate result

/-- Contextual matching is a source computation, independent of the wire
provider which later implements support-indexed substitution. -/
def SupportedMatch (model : Model) {SpaceName : Type uSpace}
    (space : SpaceName) (pattern template : Pattern)
    (support : ContextSupport.Support) (depth : Nat) :
    Computation (RevisionedSpaces SpaceName) Pattern :=
  SupportedMatchArticle model space pattern template support depth

/-- A contextual continuation binds its actual producer answer, transports
captured values at their declared support and invokes the selected activation
profile.  World threading is the same proof-relevant `Bind` as ordinary let. -/
def SupportedLet {World : Type uWorld} (model : Model)
    (activate : Pattern → Computation World Pattern)
    (support : ContextSupport.Support) (depth : Nat)
    (pattern : Pattern) (producer : Computation World Pattern)
    (body : Pattern) : Computation World Pattern :=
  Bind producer fun value before after result =>
    Σ instantiated, SupportedLetBinding model support depth
      pattern body value instantiated ×
      Eval activate instantiated before after result

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
open Mettapedia.Languages.FiniteChoice.Emptiness

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

/-- On the singleton closed world, selecting every row is also an exact
frontier for the stored fact. -/
theorem selectAllCandidates_exactForFact :
    ExistenceObserver.CandidateExact
      (structuralModel fun _ => 0) (pattern := fact)
      selectAllCandidates := by
  intro candidate _selected
  constructor
  · intro _matched
    have occurs := candidate.atomOccurrence_exists
    by_contra different
    simp [worldAfterAdd, emptyWorld, addAtomWorld, different] at occurs
  · intro equal
    refine ⟨[], 0, ?_⟩
    simp [equal, structuralModel, fact, matchPattern]
    rw [matchArgs.eq_1]
    simp

/-- A complete selector for an open pattern is not thereby an exact
structural-membership frontier: the variable pattern matches the stored fact
without being structurally equal to it. -/
theorem selectAllCandidates_not_exactForOpenPattern :
    ¬ ExistenceObserver.CandidateExact
      (structuralModel fun _ => 0) (pattern := anyPattern)
      selectAllCandidates := by
  intro frontierExact
  let candidate : CandidateOccurrence worldAfterAdd false := {
    candidate := matchFactAfterAdd.event.candidate
    atomOccurrence := matchFactAfterAdd.event.atomOccurrence
    atomOccurrence_exists := matchFactAfterAdd.event.atomOccurrence_exists }
  have equal := (frontierExact candidate ()).mp
    ⟨matchFactAfterAdd.event.bindings,
      matchFactAfterAdd.event.matchOccurrence,
      matchFactAfterAdd.event.matchOccurrence_exists⟩
  change fact = anyPattern at equal
  simp [fact, anyPattern] at equal

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

#print axioms ExistenceObserver.hasMatch_iff_frontierContainsPattern
#print axioms ExistenceObserver.hasMatchAnswer_iff_hasMatch
#print axioms ExistenceObserver.noMatchAnswer_iff_frontierAbsent
#print axioms ExistenceObserver.collectOnce_empty_iff_anyFalse
#print axioms Canary.selectAllCandidates_exactForFact
#print axioms Canary.selectAllCandidates_not_exactForOpenPattern



open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation (ProgramCommand Program)
open Mettapedia.Languages.MeTTa.MeTTaZero

/-- The complete source occurrence bag uses the original world's contents,
source matcher and checked continuation operation. It has no enumeration order. -/
def matchBag (world : RevisionedSpaces String) (space : String)
    (pattern template : Pattern) : Multiset Pattern :=
  (world.contents space).bind fun candidate =>
    Multiset.filterMap (fun bindings => applyBindingsGround? bindings template)
      (structuralModel.matchAtoms pattern candidate)


/-- The exact reflective atom installed by an admitted declaration.  This
relation does not itself assert full type inference or conditional-rule activation. -/
inductive DeclarationAtom : ProgramCommand Pattern → Pattern → Prop where
  | fact (atom : Pattern) : DeclarationAtom (.fact atom) atom
  | equation (left right : Pattern) :
      DeclarationAtom (.defineEq left right) (.apply "=" [left, right])
  | type (term type : Pattern) :
      DeclarationAtom (.defineType term type) (.apply ":" [term, type])
  | relation (name : String) (arguments : List Pattern) :
      DeclarationAtom (.relationFact name arguments) (.apply "relation!" (.apply name [] :: arguments))
  | builtin (name : String) (arguments : List Pattern) :
      DeclarationAtom (.builtinFact name arguments) (.apply "builtin!" (.apply name [] :: arguments))

def declarationAtom? : ProgramCommand Pattern → Option Pattern
  | .fact atom => some atom
  | .defineEq left right => some (.apply "=" [left, right])
  | .defineType term type => some (.apply ":" [term, type])
  | .relationFact name arguments => some (.apply "relation!" (.apply name [] :: arguments))
  | .builtinFact name arguments => some (.apply "builtin!" (.apply name [] :: arguments))
  | _ => none

@[simp] theorem declarationAtom?_exact (command : ProgramCommand Pattern) (atom : Pattern) :
    declarationAtom? command = some atom ↔ DeclarationAtom command atom := by
  constructor
  · cases command <;> simp only [declarationAtom?, Option.some.injEq, reduceCtorEq] <;>
      intro same <;> try contradiction
    all_goals subst atom
    · exact .fact _
    · exact .equation _ _
    · exact .type _ _
    · exact .relation _ _
    · exact .builtin _ _
  · intro declaration
    cases declaration <;> rfl

/-- Declared types are active schemas: match the declaration's subject
against the requested subject and instantiate its type.  No fresh metavariable
is synthesized, so user names cannot collide with a private query variable. -/
def sourceDeclaredTypes (world : RevisionedSpaces String) (current : String)
    (subject : Pattern) : Multiset Pattern :=
  (world.contents current).bind fun candidate =>
    match candidate with
    | .apply ":" [term, type] =>
        (structuralModel.matchAtoms term subject).map fun bindings => applyBindings bindings type
    | _ => 0

/-- Basic read-only activation of the selected finite profile.  Quotation
suppresses activation; named matching retains checked-ground continuations;
reflective enumeration and declared-type lookup read the current world.
The fallback is the original one-step Zero evaluation, not normalization. -/
def sourceReadAnswers (world : RevisionedSpaces String) (current : String) :
    Pattern → Multiset Pattern
  | .apply "quote" [subject] => {subject}
  | .apply "match" [.apply space [], pattern, template] => matchBag world space pattern template
  | .apply "get-atoms" [.apply space []] => world.contents space
  | .apply "get-type" [subject] => sourceDeclaredTypes world current subject
  | subject => evaluateOne structuralModel (world.contents current) subject

/-- A single read-only patterned `let` activation.  Its value and continuation
use the basic activation above.  This scope does not claim nested recursive
normalization or effectful continuation scheduling. -/
def sourceEvalAnswers (world : RevisionedSpaces String) (current : String) :
    Pattern → Multiset Pattern
  | .apply "let" [pattern, value, body] =>
      (sourceReadAnswers world current value).bind fun result =>
        (structuralModel.matchAtoms pattern result).bind fun bindings =>
          match applyBindingsGround? bindings body with
          | none => 0
          | some instantiated => sourceReadAnswers world current instantiated
  | subject => sourceReadAnswers world current subject

/-- Empty completed answers and literal uninterpreted commands are distinct. -/
inductive CommandObservation where
  | answers (values : Multiset Pattern)
  | retained (command : ProgramCommand Pattern)
deriving DecidableEq

/-- The command families consumed by this activation stage.  Literal storage
of declarations does not discharge their richer typing/rule effects. -/
def CommandHandled : ProgramCommand Pattern → Prop
  | .empty | .eval _ | .fact _ | .defineEq _ _ | .defineType _ _ |
      .relationFact _ _ | .builtinFact _ _ | .addAtom (.apply _ []) _ => True
  | _ => False

instance (command : ProgramCommand Pattern) : Decidable (CommandHandled command) := by
  unfold CommandHandled
  split <;> infer_instance

/-- A literal persistent publication is an effectful activation, never the
read-only evaluator's fallback. -/
def ReadOnlySubject : Pattern → Prop
  | .apply "add-atom" [.apply _ [], _] => False
  | _ => True

/-- Independent source transition for one actual parsed command. -/
inductive CommandDerivation (current : String) :
    ProgramCommand Pattern → RevisionedSpaces String → RevisionedSpaces String →
      CommandObservation → Type where
  | empty (world : RevisionedSpaces String) :
      CommandDerivation current .empty world world (.answers 0)
  | declaration (world : RevisionedSpaces String) (command : ProgramCommand Pattern)
      (atom : Pattern) (declared : DeclarationAtom command atom) :
      CommandDerivation current command world (addAtomWorld world current atom) (.answers 0)
  | eval (world : RevisionedSpaces String) (subject : Pattern)
      (readOnly : ReadOnlySubject subject) :
      CommandDerivation current (.eval subject) world world
        (.answers (sourceEvalAnswers world current subject))
  | evalPublish (world : RevisionedSpaces String) (space : String) (atom : Pattern) :
      CommandDerivation current (.eval (.apply "add-atom" [.apply space [], atom])) world
        (addAtomWorld world space atom) (.answers {.apply "True" []})
  | publish (world : RevisionedSpaces String) (space : String) (atom : Pattern) :
      CommandDerivation current (.addAtom (.apply space []) atom) world
        (addAtomWorld world space atom) (.answers 0)
  | retained (world : RevisionedSpaces String) (command : ProgramCommand Pattern)
      (unhandled : ¬ CommandHandled command) :
      CommandDerivation current command world world (.retained command)

/-- Source row order is causal; each row's answers remain an unordered bag. -/
inductive ProgramDerivation (current : String) :
    Program Pattern → RevisionedSpaces String → RevisionedSpaces String →
      List (Nat × CommandObservation) → Type where
  | nil (world : RevisionedSpaces String) : ProgramDerivation current [] world world []
  | cons (line : Nat) (command : ProgramCommand Pattern) (rest : Program Pattern)
      (before middle after : RevisionedSpaces String)
      (observation : CommandObservation) (observations : List (Nat × CommandObservation))
      (first : CommandDerivation current command before middle observation)
      (remaining : ProgramDerivation current rest middle after observations) :
      ProgramDerivation current ((line, command) :: rest) before after
        ((line, observation) :: observations)

/-- Every source row has exactly its original causal location in the
observation trace.  This statement imposes no order on a row's answer bag. -/
theorem ProgramDerivation.sourceLines {current : String} {program : Program Pattern}
    {before after : RevisionedSpaces String} {observations : List (Nat × CommandObservation)}
    (derivation : ProgramDerivation current program before after observations) :
    observations.map Prod.fst = program.map Prod.fst := by
  induction derivation with
  | nil => rfl
  | cons line command rest before middle after observation observations first remaining ih =>
      simp only [List.map_cons, ih]

/-- Native source execution never rolls back the causal world revision. -/
theorem CommandDerivation.revision_mono {current : String} {command : ProgramCommand Pattern}
    {before after : RevisionedSpaces String} {observation : CommandObservation}
    (derivation : CommandDerivation current command before after observation) :
    before.revision ≤ after.revision := by
  cases derivation <;> simp [addAtomWorld]

theorem ProgramDerivation.revision_mono {current : String} {program : Program Pattern}
    {before after : RevisionedSpaces String} {observations : List (Nat × CommandObservation)}
    (derivation : ProgramDerivation current program before after observations) :
    before.revision ≤ after.revision := by
  induction derivation with
  | nil => exact Nat.le_refl _
  | cons line command rest before middle after observation observations first remaining ih =>
      exact first.revision_mono.trans ih



open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef

universe u

/-- Transform payloads without changing causal revisions or space names. -/
def RevisionedSpaces.mapPayloads {SpaceName : Type u} (transform : Pattern → Pattern)
    (world : RevisionedSpaces SpaceName) : RevisionedSpaces SpaceName where
  revision := world.revision
  contents := fun space => (world.contents space).map transform

@[ext] theorem RevisionedSpaces.ext {SpaceName : Type u} {first second : RevisionedSpaces SpaceName}
    (revision : first.revision = second.revision)
    (contents : ∀ space, first.contents space = second.contents space) : first = second := by
  cases first
  cases second
  cases revision
  congr 1
  funext space
  exact contents space

@[simp] theorem RevisionedSpaces.mapPayloads_id {SpaceName : Type u} (world : RevisionedSpaces SpaceName) :
    world.mapPayloads id = world := by
  apply RevisionedSpaces.ext
  · rfl
  · intro space
    simp [mapPayloads]

@[simp] theorem RevisionedSpaces.mapPayloads_comp {SpaceName : Type u} (first second : Pattern → Pattern)
    (world : RevisionedSpaces SpaceName) :
    (world.mapPayloads first).mapPayloads second = world.mapPayloads (second ∘ first) := by
  apply RevisionedSpaces.ext
  · rfl
  · intro space
    simp [mapPayloads, Multiset.map_map]

/-- Persistent publication commutes with the actual payload action. -/
theorem RevisionedSpaces.mapPayloads_publish {SpaceName : Type u} [DecidableEq SpaceName]
    (transform : Pattern → Pattern) (world : RevisionedSpaces SpaceName) (space : SpaceName) (atom : Pattern) :
    (addAtomWorld world space atom).mapPayloads transform =
      addAtomWorld (world.mapPayloads transform) space (transform atom) := by
  apply RevisionedSpaces.ext
  · rfl
  · intro read
    by_cases same : read = space <;> simp [mapPayloads, addAtomWorld, same]

@[simp] theorem RevisionedSpaces.mapPayloads_card {SpaceName : Type u}
    (transform : Pattern → Pattern) (world : RevisionedSpaces SpaceName) (space : SpaceName) :
    ((world.mapPayloads transform).contents space).card = (world.contents space).card := by
  simp [mapPayloads]

/-- Value-class occurrence ordinals transport unchanged under injective payload
maps. Without this hypothesis, different value classes can merge. -/
theorem RevisionedSpaces.mapPayloads_count {SpaceName : Type u}
    (transform : Pattern → Pattern) (injective : Function.Injective transform)
    (world : RevisionedSpaces SpaceName) (space : SpaceName) (atom : Pattern) :
    Multiset.count (transform atom) ((world.mapPayloads transform).contents space) =
      Multiset.count atom (world.contents space) :=
  Multiset.count_map_eq_count' transform _ injective atom

/-- Quotation suppresses activation, while ordinary environment substitution
still enters its payload, as in the actual PeTTa quote rule. -/
theorem quote_support_substitution (before after : RevisionedSpaces String) (current : String)
    (support : ContextSupport.Support) (assignment : ContextSupport.Assignment)
    (depth : Nat) (subject : Pattern) :
    sourceReadAnswers after current
        (ContextSupport.substituteAt support assignment depth (.apply "quote" [subject])) =
      (sourceReadAnswers before current (.apply "quote" [subject])).map
        (ContextSupport.substituteAt support assignment depth) := by
  simp [ContextSupport.substituteAt, sourceReadAnswers]



end Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval



/-!
Parsed declaration installation is separate from admission and execution.
The original core command and rule converter retain the actual premise list;
compiled plans retain declaration positions independently of rule names.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation

open Mettapedia.OSLF.MeTTaIL
open Syntax GeneralExecutionAdmission
open Mettapedia.Languages.MeTTa.PeTTa.ProfileBridge

abbrev State := Snapshot × RevisionedSpaces String
abbrev Command := MeTTailCore.MeTTaSyntax.SyntaxCommand
abbrev CoreRule := MeTTailCore.MeTTaIL.Syntax.RewriteRule

/-- Keep the source converter as the only raw premise parser. -/
def parsedRule? (name : String) (command : Command) : Option RewriteRule :=
  (MeTTailCore.MeTTaSyntax.syntaxRule? name command).map coreToSpecRewriteRule

/-- Installing a declaration does not certify its grammar, provider flow or
availability for execution. Those are the existing admission plan's jobs. -/
def installSnapshot (before : Snapshot) (rule : RewriteRule) : Snapshot :=
  {before with language := before.language.addRewrite rule}

/-- The command's literal source data remains available to reflection. -/
def ruleAtom : Command → Option Pattern
  | .defineEq left right =>
      declarationAtom? (.defineEq (coreToSpecPattern left) (coreToSpecPattern right))
  | .defineRule left right premises =>
      some (.apply "rule!" (coreToSpecPattern left :: coreToSpecPattern right ::
        premises.map coreToSpecPattern))
  | _ => none

/-- Independent source installation: the original parsed declaration supplies
its actual structured rule, which is appended at its own declaration position.
Neither a compiled plan nor an evaluator result defines this relation. -/
inductive Installed (current name : String) (command : Command) :
    State → State → Type where
  | declaration (before : State) (authored : CoreRule) (literal : Pattern)
      (parsed : MeTTailCore.MeTTaSyntax.syntaxRule? name command = some authored)
      (quoted : ruleAtom command = some literal) :
      Installed current name command before
        (installSnapshot before.1 (coreToSpecRewriteRule authored),
          addAtomWorld before.2 current literal)

theorem parsed_has_literal (name : String) (command : Command) (authored : CoreRule)
    (parsed : MeTTailCore.MeTTaSyntax.syntaxRule? name command = some authored) :
    ∃ literal, ruleAtom command = some literal := by
  cases command <;>
    try { simp only [MeTTailCore.MeTTaSyntax.syntaxRule?, reduceCtorEq] at parsed }
  all_goals exact ⟨_, rfl⟩

theorem parsedRule?_source (name : String) (command : Command) (rule : RewriteRule) :
    parsedRule? name command = some rule ↔
      ∃ authored : CoreRule,
        MeTTailCore.MeTTaSyntax.syntaxRule? name command = some authored ∧
        coreToSpecRewriteRule authored = rule := by
  simp only [parsedRule?, Option.map_eq_some_iff]

/-- The guarded clause retains every original structured premise occurrence. -/
theorem parsed_guarded_fields (name : String)
    (left right : MeTTailCore.MeTTaIL.Syntax.Pattern)
    (terms : List MeTTailCore.MeTTaIL.Syntax.Pattern)
    (rule : RewriteRule)
    (parsed : parsedRule? name (.defineRule left right terms) = some rule) :
    ∃ premises : List MeTTailCore.MeTTaIL.Syntax.Premise,
      terms.mapM MeTTailCore.MeTTaSyntax.syntaxPremise? = some premises ∧
      rule.name = name ∧ rule.left = coreToSpecPattern left ∧
      rule.right = coreToSpecPattern right ∧
      rule.premises = premises.map coreToSpecPremise := by
  obtain ⟨authored, decoded, same⟩ := (parsedRule?_source _ _ _).mp parsed
  subst rule
  simp only [MeTTailCore.MeTTaSyntax.syntaxRule?, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at decoded
  obtain ⟨premises, checked, returned⟩ := decoded
  cases Option.some.inj returned
  exact ⟨premises, checked, rfl, rfl, rfl, rfl⟩

@[simp] theorem installSnapshot_grammar (before : Snapshot) (rule : RewriteRule) :
    (installSnapshot before rule).language.terms = before.language.terms := rfl

@[simp] theorem installSnapshot_freeTypes (before : Snapshot) (rule : RewriteRule) :
    (installSnapshot before rule).freeTypes = before.freeTypes := rfl

@[simp] theorem installSnapshot_provider (before : Snapshot) (rule : RewriteRule) :
    (installSnapshot before rule).provider = before.provider := rfl

/-- Existing declaration occurrences retain their exact original positions. -/
theorem installSnapshot_old (before : Snapshot) (rule : RewriteRule) (index : Nat)
    (earlier : index < before.language.rewrites.length) :
    (installSnapshot before rule).language.rewrites[index]? =
      before.language.rewrites[index]? := by
  simp only [installSnapshot, LanguageDef.addRewrite]
  exact List.getElem?_append_left earlier

/-- The new declaration has its own position even if its name/body repeats. -/
@[simp] theorem installSnapshot_new (before : Snapshot) (rule : RewriteRule) :
    (installSnapshot before rule).language.rewrites[before.language.rewrites.length]? = some rule := by
  simp [installSnapshot, LanguageDef.addRewrite]

/-- Original binding elaboration is allowed to add typing information; it
cannot erase, reorder or replace source premises. -/
theorem compiled_new_guarded_fields (before : Snapshot) (permissions : Permissions)
    (name : String) (left right : MeTTailCore.MeTTaIL.Syntax.Pattern)
    (terms : List MeTTailCore.MeTTaIL.Syntax.Pattern) (rule : RewriteRule)
    (parsed : parsedRule? name (.defineRule left right terms) = some rule)
    (selected : RulePlan)
    (member : selected ∈ (GeneralExecutionAdmission.compile
      (installSnapshot before rule) permissions).rules)
    (position : selected.declarationIndex = before.language.rewrites.length) :
    ∃ premises : List MeTTailCore.MeTTaIL.Syntax.Premise,
      terms.mapM MeTTailCore.MeTTaSyntax.syntaxPremise? = some premises ∧
      selected.rule.name = name ∧ selected.rule.left = coreToSpecPattern left ∧
      selected.rule.right = coreToSpecPattern right ∧
      selected.rule.premises = premises.map coreToSpecPremise := by
  obtain ⟨actual, index, declared, _, compiled⟩ := compiled_rule_origin member
  have readout := rulePlan_readout compiled
  have indexSame : index = before.language.rewrites.length := readout.1.symm.trans position
  subst index
  have actualPosition := List.mk_mem_zipIdx_iff_getElem?.mp declared
  rw [installSnapshot_new] at actualPosition
  have actualSame : actual = rule := Option.some.inj actualPosition.symm
  subst actual
  have fields := parsed_guarded_fields name left right terms rule parsed
  obtain ⟨premises, checked, named, input, output, guards⟩ := fields
  have preserved := GeneralRuleBindingInference.elaborate_source selected.binding selected.authored
  rw [← readout.2.1] at named input output guards
  exact ⟨premises, checked, preserved.1.trans named, preserved.2.1.trans input,
    preserved.2.2.1.trans output, preserved.2.2.2.trans guards⟩

end Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation



set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (SourceGuard SourceGuardHolds Subst)

/-- Source spelling of an Atom freshness guard, without reinterpreting its
subject through the non-injective ordinary Pattern projection. -/
inductive AtomFreshnessForm : Atom → SourceGuard → Prop where
  | fresh (name : String) (subject : Atom) :
      AtomFreshnessForm (.expression [.symbol "fresh", .var name, subject])
        (.freshness name subject)

def lowerAtomFreshness? : Atom → Option SourceGuard
  | .expression [.symbol "fresh", .var name, subject] => some (.freshness name subject)
  | _ => none

@[simp] theorem lowerAtomFreshness?_exact (atom : Atom) (guard : SourceGuard) :
    lowerAtomFreshness? atom = some guard ↔ AtomFreshnessForm atom guard := by
  constructor
  · intro lowered
    unfold lowerAtomFreshness? at lowered
    split at lowered
    · cases lowered
      exact .fresh _ _
    · contradiction
  · intro formed
    cases formed
    rfl

inductive AtomFreshnessObservation where
  | held
  | failed
  | retained (original : Atom)
  deriving DecidableEq, Repr

/-- An independent source judgment distinguishes failed source freshness
from syntax which this service does not interpret. -/
inductive AtomFreshnessOutcome (substitution : Subst) (atom : Atom) :
    AtomFreshnessObservation → Prop where
  | held {guard : SourceGuard} (formed : AtomFreshnessForm atom guard)
      (holds : SourceGuardHolds substitution guard) :
      AtomFreshnessOutcome substitution atom .held
  | failed {guard : SourceGuard} (formed : AtomFreshnessForm atom guard)
      (fails : ¬ SourceGuardHolds substitution guard) :
      AtomFreshnessOutcome substitution atom .failed
  | retained (unknown : ∀ guard, ¬ AtomFreshnessForm atom guard) :
      AtomFreshnessOutcome substitution atom (.retained atom)

/-- After original substitution has resolved the guard arguments, freshness
is a predicate of the actual name value and actual guest data. -/
inductive ResolvedAtomFreshness : Atom → Atom → Prop where
  | variableName (name : String) (subject : Atom)
      (fresh : name ∉ Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars subject) :
      ResolvedAtomFreshness (.var name) subject

end Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation



set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)

/-- The two original matcher entry points differ on quoted constructor syntax. -/
inductive AtomMatchMode where
  | value
  | binding
  deriving DecidableEq, Repr

/-- Source matching is the independent judgment for the selected entry point. -/
def AtomMatched (mode : AtomMatchMode) (initial : Subst)
    (pattern value : Atom) (final : Subst) : Prop :=
  match mode with
  | .value => ValueMatch initial pattern value final
  | .binding => BindingMatch initial pattern value final

/-- Failure is the absence of a source match, not an unreadable input. -/
inductive AtomMatchOutcome (mode : AtomMatchMode) (initial : Subst)
    (pattern value : Atom) : Option Subst → Prop where
  | matched {final : Subst} (source : AtomMatched mode initial pattern value final) :
      AtomMatchOutcome mode initial pattern value (some final)
  | refused (source : ∀ final, ¬ AtomMatched mode initial pattern value final) :
      AtomMatchOutcome mode initial pattern value none

end Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation



set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation (ProgramCommand)

abbrev Command := ProgramCommand Atom

/-- Source declarations retain actual Atom syntax, including the difference
between a symbol and a nullary expression. Guard interpretation is subsequent
activation; retaining a rule declaration does not discharge its guards. -/
inductive Declaration : Command → Atom → Prop where
  | fact (atom : Atom) : Declaration (.fact atom) atom
  | equation (left right : Atom) :
      Declaration (.defineEq left right) (.expression [.symbol "=", left, right])
  | rule (left right : Atom) (guards : List Atom) :
      Declaration (.defineRule left right guards)
        (.expression (.symbol "rule!" :: left :: right :: guards))
  | type (term type : Atom) :
      Declaration (.defineType term type) (.expression [.symbol ":", term, type])
  | relation (name : String) (arguments : List Atom) :
      Declaration (.relationFact name arguments)
        (.expression (.symbol "relation!" :: .symbol name :: arguments))
  | builtin (name : String) (arguments : List Atom) :
      Declaration (.builtinFact name arguments)
        (.expression (.symbol "builtin!" :: .symbol name :: arguments))

def declaration? : Command → Option Atom
  | .fact atom => some atom
  | .defineEq left right => some (.expression [.symbol "=", left, right])
  | .defineRule left right guards =>
      some (.expression (.symbol "rule!" :: left :: right :: guards))
  | .defineType term type => some (.expression [.symbol ":", term, type])
  | .relationFact name arguments =>
      some (.expression (.symbol "relation!" :: .symbol name :: arguments))
  | .builtinFact name arguments =>
      some (.expression (.symbol "builtin!" :: .symbol name :: arguments))
  | _ => none

@[simp] theorem declaration?_exact (command : Command) (atom : Atom) :
    declaration? command = some atom ↔ Declaration command atom := by
  constructor
  · cases command <;> simp only [declaration?, Option.some.injEq, reduceCtorEq] <;>
      intro same <;> try contradiction
    all_goals subst atom
    · exact .fact _
    · exact .equation _ _
    · exact .rule _ _ _
    · exact .type _ _
    · exact .relation _ _
    · exact .builtin _ _
  · intro source
    cases source <;> rfl

/-- The actual store is reused. The surrounding fields belong to source
command sequencing: ambient names, the selected target, the future execution
budget and the public revision. No second space or cell semantics is defined. -/
structure State where
  store : Effects.State
  bindings : Subst := []
  current : NamedSpaces.Handle := .self
  fuel : Nat
  revision : Nat := 0
  input : List Atom := []
  output : List Atom := []

/-- A command may schedule an existing computation or module acquisition.
Those continuations remain distinct from completed command observations. -/
inductive Action where
  | done (answers : List Atom)
  | evaluate (configuration : Eval.Configuration)
  | importModule (target : NamedSpaces.Handle) (module : Atom)
  | retained (original : Command)
  | fault (reason : Effects.Fault)

def State.withStore (before : State) (after : Effects.State) : State :=
  { before with store := after, revision := before.revision + 1 }

def State.evalConfiguration (before : State) (term : Atom) : Eval.Configuration where
  state := before.store
  control := .evaluate before.bindings term
  input := before.input
  output := before.output

/-- Source space arguments are resolved using the original first-match
substitution before the original opaque-handle reader is applied. -/
def resolvedHandle? (before : State) (space : Atom) : Option NamedSpaces.Handle :=
  Effects.readHandle (applySubst before.bindings space)

/-- Sequential source command meaning. Each constructor gives the original
store operation or the exact continuation to be performed. Module acquisition
and evaluation are not declared complete by these dispatch rules. -/
inductive Dispatch : Command → State → State → Action → Prop where
  | empty (before : State) : Dispatch .empty before before (.done [])
  | declaration {command : Command} {atom : Atom} {before : State} {after : Effects.State}
      (declared : Declaration command atom)
      (inserted : Effects.insert before.store before.current atom = some after) :
      Dispatch command before (before.withStore after) (.done [])
  | declarationFault {command : Command} {atom : Atom} {before : State}
      (declared : Declaration command atom)
      (unallocated : Effects.insert before.store before.current atom = none) :
      Dispatch command before before (.fault .invalidSpace)
  | eval (before : State) (term : Atom) :
      Dispatch (.eval term) before before (.evaluate (before.evalConfiguration term))
  | fuel (before : State) (amount : Nat) :
      Dispatch (.setFuel amount) before {before with fuel := amount} (.done [])
  | allocate (before : State) (name : String) :
      Dispatch (.newSpace name) before
        {before.withStore (before.store.allocate []).2 with
          bindings := (name, Effects.handleValue (before.store.allocate []).1) :: before.bindings}
        (.done [Effects.handleValue (before.store.allocate []).1])
  | add {before : State} {space atom : Atom} {handle : NamedSpaces.Handle}
      {after : Effects.State} (resolved : resolvedHandle? before space = some handle)
      (inserted : Effects.insert before.store handle (applySubst before.bindings atom) = some after) :
      Dispatch (.addAtom space atom) before (before.withStore after) (.done [Effects.boolean true])
  | addUnknown {before : State} {space atom : Atom}
      (unresolved : resolvedHandle? before space = none) :
      Dispatch (.addAtom space atom) before before (.fault .invalidSpace)
  | addUnallocated {before : State} {space atom : Atom} {handle : NamedSpaces.Handle}
      (resolved : resolvedHandle? before space = some handle)
      (unallocated : Effects.insert before.store handle (applySubst before.bindings atom) = none) :
      Dispatch (.addAtom space atom) before before (.fault .invalidSpace)
  | remove {before : State} {space atom : Atom} {after : Effects.State} {answers : List Atom}
      (removed : StdLib.apply before.store "remove-atom"
        [applySubst before.bindings space, applySubst before.bindings atom] = .ok (after, answers)) :
      Dispatch (.removeAtom space atom) before (before.withStore after) (.done answers)
  | removeFault {before : State} {space atom : Atom} {reason : Effects.Fault}
      (failed : StdLib.apply before.store "remove-atom"
        [applySubst before.bindings space, applySubst before.bindings atom] = .error reason) :
      Dispatch (.removeAtom space atom) before before (.fault reason)
  | importing {before : State} {space module : Atom} {handle : NamedSpaces.Handle}
      (resolved : resolvedHandle? before space = some handle) :
      Dispatch (.import space module) before before
        (.importModule handle (applySubst before.bindings module))
  | importUnknown {before : State} {space module : Atom}
      (unresolved : resolvedHandle? before space = none) :
      Dispatch (.import space module) before before (.fault .invalidSpace)
  | directive (before : State) (name : String) (arguments : List Atom) :
      Dispatch (.directive name arguments) before before (.retained (.directive name arguments))

def dispatch (command : Command) (before : State) : State × Action :=
  match declaration? command with
  | some atom =>
      match Effects.insert before.store before.current atom with
      | some after => (before.withStore after, .done [])
      | none => (before, .fault .invalidSpace)
  | none =>
      match command with
      | .empty => (before, .done [])
      | .eval term => (before, .evaluate (before.evalConfiguration term))
      | .setFuel amount => ({before with fuel := amount}, .done [])
      | .newSpace name =>
          let allocated := before.store.allocate []
          ({before.withStore allocated.2 with
             bindings := (name, Effects.handleValue allocated.1) :: before.bindings},
            .done [Effects.handleValue allocated.1])
      | .addAtom space atom =>
          match resolvedHandle? before space with
          | none => (before, .fault .invalidSpace)
          | some handle =>
              match Effects.insert before.store handle (applySubst before.bindings atom) with
              | none => (before, .fault .invalidSpace)
              | some after => (before.withStore after, .done [Effects.boolean true])
      | .removeAtom space atom =>
          match StdLib.apply before.store "remove-atom"
              [applySubst before.bindings space, applySubst before.bindings atom] with
          | .ok (after, answers) => (before.withStore after, .done answers)
          | .error reason => (before, .fault reason)
      | .import space module =>
          match resolvedHandle? before space with
          | none => (before, .fault .invalidSpace)
          | some handle => (before, .importModule handle (applySubst before.bindings module))
      | .directive name arguments => (before, .retained (.directive name arguments))
      | .fact _ | .defineEq _ _ | .defineRule _ _ _ | .defineType _ _ |
          .relationFact _ _ | .builtinFact _ _ => (before, .retained command)

/-- All fourteen command shapes reach their independently specified source
operation or continuation. The unreachable retained branches do not serve as
an implementation of any declaration. -/
theorem dispatch_sound (command : Command) (before : State) :
    Dispatch command before (dispatch command before).1 (dispatch command before).2 := by
  unfold dispatch
  cases declared : declaration? command with
  | some atom =>
      dsimp only
      have source := (declaration?_exact command atom).mp declared
      cases inserted : Effects.insert before.store before.current atom with
      | none => exact .declarationFault source inserted
      | some after => exact .declaration source inserted
  | none =>
      dsimp only
      cases command with
      | empty => exact .empty before
      | eval term => exact .eval before term
      | setFuel amount => exact .fuel before amount
      | newSpace name => exact .allocate before name
      | addAtom space atom =>
          dsimp only
          cases resolved : resolvedHandle? before space with
          | none => exact .addUnknown resolved
          | some handle =>
              dsimp only
              cases inserted : Effects.insert before.store handle (applySubst before.bindings atom) with
              | none => exact .addUnallocated resolved inserted
              | some after => exact .add resolved inserted
      | removeAtom space atom =>
          dsimp only
          cases removed : StdLib.apply before.store "remove-atom"
              [applySubst before.bindings space, applySubst before.bindings atom] with
          | error reason => exact .removeFault removed
          | ok result => rcases result with ⟨after, answers⟩; exact .remove removed
      | «import» space module =>
          dsimp only
          cases resolved : resolvedHandle? before space with
          | none => exact .importUnknown resolved
          | some handle => exact .importing resolved
      | directive name arguments => exact .directive before name arguments
      | fact _ => simp only [declaration?, reduceCtorEq] at declared
      | defineEq _ _ => simp only [declaration?, reduceCtorEq] at declared
      | defineRule _ _ _ => simp only [declaration?, reduceCtorEq] at declared
      | defineType _ _ => simp only [declaration?, reduceCtorEq] at declared
      | relationFact _ _ => simp only [declaration?, reduceCtorEq] at declared
      | builtinFact _ _ => simp only [declaration?, reduceCtorEq] at declared

/-- Source derivations select exactly the executed dispatch result. -/
theorem dispatch_complete {command : Command} {before after : State} {action : Action}
    (source : Dispatch command before after action) : dispatch command before = (after, action) := by
  cases source with
  | empty => rfl
  | declaration declared inserted =>
      simp only [dispatch, (declaration?_exact _ _).mpr declared, inserted]
  | declarationFault declared unallocated =>
      simp only [dispatch, (declaration?_exact _ _).mpr declared, unallocated]
  | eval => rfl
  | fuel => rfl
  | allocate => rfl
  | add resolved inserted => simp only [dispatch, declaration?, resolved, inserted]
  | addUnknown unresolved => simp only [dispatch, declaration?, unresolved]
  | addUnallocated resolved unallocated => simp only [dispatch, declaration?, resolved, unallocated]
  | remove removed => simp only [dispatch, declaration?, removed]
  | removeFault failed => simp only [dispatch, declaration?, failed]
  | importing resolved => simp only [dispatch, declaration?, resolved]
  | importUnknown unresolved => simp only [dispatch, declaration?, unresolved]
  | directive => rfl

@[simp] theorem dispatch_exact (command : Command) (before after : State) (action : Action) :
    dispatch command before = (after, action) ↔ Dispatch command before after action := by
  constructor
  · intro result
    have source := dispatch_sound command before
    rw [result] at source
    exact source
  · exact dispatch_complete

/-- Rule publication preserves every source guard occurrence, independently
of whether a later guard service can interpret it. -/
theorem guarded_rule_publication {before after : State} {left right : Atom} {guards : List Atom}
    (published : Dispatch (.defineRule left right guards) before after (.done [])) :
    ∃ oldRows,
      before.store.read before.current = some oldRows ∧
      after.store.read before.current =
        some (oldRows ++ [.expression (.symbol "rule!" :: left :: right :: guards)]) ∧
      after.revision = before.revision + 1 := by
  cases published with
  | declaration declared inserted =>
      cases declared
      obtain ⟨oldRows, allocated, stored⟩ := Effects.insert_reads_back inserted
      exact ⟨oldRows, allocated, stored, rfl⟩

/-- Source command sequencing cannot silently lower a completed import or
completed evaluation from a dispatch continuation alone. -/
theorem eval_schedules_original (before : State) (term : Atom) :
    dispatch (.eval term) before = (before, .evaluate {
      state := before.store, control := .evaluate before.bindings term,
      input := before.input, output := before.output }) := rfl


/-- These command primitives do not write named state cells. Allocation and
space mutation retain the original finite cell support. -/
theorem Dispatch.cells {command : Command} {before after : State} {action : Action}
    (source : Dispatch command before after action) : after.store.cells = before.store.cells := by
  cases source
  all_goals first
    | rfl
    | exact Effects.insert_preserves_cells (by assumption)
    | skip
  case remove removed =>
    rcases StdLib.successful_apply_cell_update removed with same | ⟨name, value, head, _, _⟩
    · exact same
    · contradiction

theorem Dispatch.emptyTail {command : Command} {before after : State} {action : Action}
    (source : Dispatch command before after action)
    (vacant : NamedSpaces.Store.EmptyTail before.store []) :
    NamedSpaces.Store.EmptyTail after.store [] := by
  cases source
  all_goals first
    | exact vacant
    | exact Effects.insert_preserves_empty_tail vacant (by assumption)
    | exact NamedSpaces.Store.allocate_emptyTail vacant
    | exact StdLib.successful_apply_empty_tail vacant (by assumption)

theorem Dispatch.revision_mono {command : Command} {before after : State} {action : Action}
    (source : Dispatch command before after action) : before.revision ≤ after.revision := by
  cases source <;> simp [State.withStore]

/-- Only the evaluation command schedules an original evaluator. Its input,
ambient substitution and already performed output remain the source values. -/
theorem Dispatch.evaluation_origin {command : Command} {before after : State}
    {configuration : Eval.Configuration}
    (source : Dispatch command before after (.evaluate configuration)) :
    ∃ term, command = .eval term ∧ after = before ∧
      configuration = before.evalConfiguration term := by
  cases source
  exact ⟨_, rfl, rfl, rfl⟩

end Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands



set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa

/-- A callable stored declaration, before interpreting any of its guards.
An ordinary equation and a guard-free rule declaration retain different
source syntax even when they authorize the same unguarded body. -/
inductive RuleDeclaration : Atom → SpaceSemantics.Equation → List Atom → Prop where
  | equation (head : String) (arguments : List Atom) (body : Atom) :
      RuleDeclaration (.expression [.symbol "=", .expression (.symbol head :: arguments), body])
        ⟨head, arguments, body⟩ []
  | guarded (head : String) (arguments : List Atom) (body : Atom) (guards : List Atom) :
      RuleDeclaration (.expression (.symbol "rule!" ::
        .expression (.symbol head :: arguments) :: body :: guards))
        ⟨head, arguments, body⟩ guards

def readRule? : Atom → Option (SpaceSemantics.Equation × List Atom)
  | .expression [.symbol "=", .expression (.symbol head :: arguments), body] =>
      some (⟨head, arguments, body⟩, [])
  | .expression (.symbol "rule!" :: .expression (.symbol head :: arguments) :: body :: guards) =>
      some (⟨head, arguments, body⟩, guards)
  | _ => none

@[simp] theorem readRule?_exact (atom : Atom) (equation : SpaceSemantics.Equation)
    (guards : List Atom) : readRule? atom = some (equation, guards) ↔
      RuleDeclaration atom equation guards := by
  constructor
  · intro read
    unfold readRule? at read
    split at read
    · cases Option.some.inj read
      exact .equation _ _ _
    · cases Option.some.inj read
      exact .guarded _ _ _ _
    · contradiction
  · intro source
    cases source <;> rfl

/-- The stored atom and its physical declaration coordinate supply authority.
A clause's name or the identity of a resulting program cannot supply it. -/
def RuleAt (rows : List Atom) (index : Nat) (equation : SpaceSemantics.Equation)
    (guards : List Atom) : Prop :=
  ∃ atom, rows[index]? = some atom ∧ RuleDeclaration atom equation guards

abbrev IndexedRule := Nat × SpaceSemantics.Equation × List Atom

/-- This list is one scheduling enumeration. The source contract retains
coordinates and duplicate occurrences and makes no global result-order claim. -/
def ruleOccurrences (rows : List Atom) : List IndexedRule :=
  rows.zipIdx.filterMap fun (atom, index) =>
    (readRule? atom).map fun (equation, guards) => (index, equation, guards)

@[simp] theorem ruleOccurrences_exact (rows : List Atom) (index : Nat)
    (equation : SpaceSemantics.Equation) (guards : List Atom) :
    (index, equation, guards) ∈ ruleOccurrences rows ↔ RuleAt rows index equation guards := by
  simp only [ruleOccurrences, List.mem_filterMap, Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨atom, actualIndex⟩, positioned, ⟨⟨actualEquation, actualGuards⟩, read, same⟩⟩
    cases same
    exact ⟨atom, List.mk_mem_zipIdx_iff_getElem?.mp positioned,
      (readRule?_exact _ _ _).mp read⟩
  · rintro ⟨atom, positioned, source⟩
    exact ⟨(atom, index), List.mk_mem_zipIdx_iff_getElem?.mpr positioned,
      (equation, guards), (readRule?_exact _ _ _).mpr source, rfl⟩

structure PreparedClause where
  declarationIndex : Nat
  equation : SpaceSemantics.Equation
  guards : List Atom
  bindings : Subst
  deriving Repr

/-- Actual original PeTTa value matching selects a clause. Guard execution
must still be earned before this preparation licenses a body evaluation. -/
inductive PreparedAt (rows : List Atom) (head : String) (values : List Atom) :
    PreparedClause → Prop where
  | matched {index : Nat} {equation : SpaceSemantics.Equation} {guards : List Atom}
      {bindings : Subst} (stored : RuleAt rows index equation guards)
      (named : equation.head = head)
      (matched : SpaceSemantics.ValueMatch [] (.expression equation.arguments)
        (.expression values) bindings) :
      PreparedAt rows head values ⟨index, equation, guards, bindings⟩

def prepareClauses (rows : List Atom) (head : String) (values : List Atom) : List PreparedClause :=
  (ruleOccurrences rows).filterMap fun (index, equation, guards) =>
    if equation.head = head then
      (SpaceSemantics.matchValue [] (.expression equation.arguments) (.expression values)).map
        fun bindings => ⟨index, equation, guards, bindings⟩
    else none

@[simp] theorem prepareClauses_exact (rows : List Atom) (head : String) (values : List Atom)
    (prepared : PreparedClause) : prepared ∈ prepareClauses rows head values ↔
      PreparedAt rows head values prepared := by
  simp only [prepareClauses, List.mem_filterMap]
  constructor
  · rintro ⟨⟨index, equation, guards⟩, stored, selected⟩
    split at selected
    next named =>
      obtain ⟨bindings, matched, same⟩ := Option.map_eq_some_iff.mp selected
      cases same
      exact .matched ((ruleOccurrences_exact _ _ _ _).mp stored) named
        (SpaceSemantics.matchValue_sound matched)
    next => contradiction
  · intro source
    cases source with
    | @matched index equation guards bindings stored named matched =>
        exact ⟨(index, equation, guards), (ruleOccurrences_exact _ _ _ _).mpr stored,
          by simp only [named, ↓reduceIte, SpaceSemantics.matchValue_complete matched, Option.map_some]⟩

/-- Preparation has original source provenance, including its guard list,
full matcher evidence and declaration coordinate. -/
theorem prepared_has_original_source {rows : List Atom} {head : String} {values : List Atom}
    {prepared : PreparedClause} (selected : prepared ∈ prepareClauses rows head values) :
    ∃ atom, rows[prepared.declarationIndex]? = some atom ∧
      RuleDeclaration atom prepared.equation prepared.guards ∧
      prepared.equation.head = head ∧
      SpaceSemantics.ValueMatch [] (.expression prepared.equation.arguments)
        (.expression values) prepared.bindings := by
  have source := (prepareClauses_exact _ _ _ _).mp selected
  cases source with
  | matched stored named matched =>
      obtain ⟨atom, positioned, declared⟩ := stored
      exact ⟨atom, positioned, declared, named, matched⟩


/-- Publishing a source rule produces a callable occurrence at its new
physical position. Repeated equal declarations still have distinct positions. -/
theorem published_guarded_occurrence {before after : State} {head : String}
    {arguments : List Atom} {body : Atom} {guards : List Atom}
    (published : Dispatch (.defineRule (.expression (.symbol head :: arguments)) body guards)
      before after (.done [])) :
    ∃ oldRows rows,
      before.store.read before.current = some oldRows ∧
      after.store.read before.current = some rows ∧
      RuleAt rows oldRows.length ⟨head, arguments, body⟩ guards ∧
      (oldRows.length, (⟨head, arguments, body⟩ : SpaceSemantics.Equation), guards)
        ∈ ruleOccurrences rows := by
  obtain ⟨oldRows, allocated, stored, _⟩ := guarded_rule_publication published
  refine ⟨oldRows, oldRows ++ [.expression (.symbol "rule!" ::
    .expression (.symbol head :: arguments) :: body :: guards)], allocated, stored, ?_, ?_⟩
  · exact ⟨_, by simp, .guarded _ _ _ _⟩
  · exact (ruleOccurrences_exact _ _ _ _).mpr ⟨_, by simp, .guarded _ _ _ _⟩

/-- A successfully prepared body has a source argument match, but no premise
here asserts its guards. The later guard continuation must provide them. -/
def PreparedClause.pendingControl (prepared : PreparedClause) : Eval.Control :=
  .evaluate prepared.bindings prepared.equation.body

end Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands



set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst SourceGuardHolds)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.OSLF.MeTTaIL.GeneralPremise (ProviderSnapshot DynamicProvider Signature signature?)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern RelationArgMode)

/-- The independently selected Atom profile adds conditional declarations to
stored equations. Data outside these exact forms remains inert. -/
inductive Clause : Atom → Atom → Atom → List Atom → Prop where
  | equation (left right : Atom) :
      Clause (.expression [.symbol "=", left, right]) left right []
  | guarded (left right : Atom) (guards : List Atom) :
      Clause (.expression (.symbol "rule!" :: left :: right :: guards)) left right guards

def readClause? : Atom → Option (Atom × Atom × List Atom)
  | .expression [.symbol "=", left, right] => some (left, right, [])
  | .expression (.symbol "rule!" :: left :: right :: guards) => some (left, right, guards)
  | _ => none

@[simp] theorem readClause?_exact (atom left right : Atom) (guards : List Atom) :
    readClause? atom = some (left, right, guards) ↔ Clause atom left right guards := by
  constructor
  · intro found
    unfold readClause? at found
    split at found
    · cases Option.some.inj found
      exact .equation _ _
    · cases Option.some.inj found
      exact .guarded _ _ _
    · contradiction
  · intro source
    cases source <;> rfl

/-- Physical source positions, including duplicate declarations, are retained
independently of any index implementation. -/
def ClauseAt (rows : List Atom) (index : Nat) (left right : Atom) (guards : List Atom) : Prop :=
  ∃ atom, rows[index]? = some atom ∧ Clause atom left right guards

/-- Both stored tuple kinds retain their own provenance. Native responses
have a separate occurrence space, even when their values equal a stored row. -/
inductive Origin where
  | relation (index : Nat)
  | builtin (index : Nat)
  | native (index : Nat)
  deriving DecidableEq, Repr

structure Environment where
  rows : List Atom
  registration : ProviderSnapshot := { signatures := [], rows := [] }
  dynamic : DynamicProvider := .empty

/-- Native input positions observe the original incoming assignment. Output
positions remain schemas until a returned row is matched in sequence. -/
inductive Inputs (initial : Subst) : List Atom → List RelationArgMode → List Pattern → Prop where
  | nil : Inputs initial [] [] []
  | input {schema : Atom} {schemas : List Atom} {modes : List RelationArgMode}
      {resolved : List Pattern} :
      Inputs initial schemas modes resolved →
      Inputs initial (schema :: schemas) (.input :: modes)
        (GroundData.encode (applySubst initial schema) :: resolved)
  | output {schema : Atom} {schemas : List Atom} {modes : List RelationArgMode}
      {resolved : List Pattern} :
      Inputs initial schemas modes resolved →
      Inputs initial (schema :: schemas) (.output :: modes) (GroundData.schema schema :: resolved)

def resolveInputs (initial : Subst) : List Atom → List RelationArgMode → Option (List Pattern)
  | [], [] => some []
  | schema :: schemas, .input :: modes =>
      (resolveInputs initial schemas modes).map
        (GroundData.encode (applySubst initial schema) :: ·)
  | schema :: schemas, .output :: modes =>
      (resolveInputs initial schemas modes).map (GroundData.schema schema :: ·)
  | _, _ => none

@[simp] theorem resolveInputs_exact (initial : Subst) (schemas : List Atom)
    (modes : List RelationArgMode) (resolved : List Pattern) :
    resolveInputs initial schemas modes = some resolved ↔ Inputs initial schemas modes resolved := by
  induction schemas generalizing modes resolved with
  | nil =>
      cases modes with
      | nil =>
          constructor
          · intro same; cases same; exact .nil
          · intro source; cases source; rfl
      | cons mode modes => constructor <;> intro impossible <;> cases impossible
  | cons schema schemas ih =>
      cases modes with
      | nil => constructor <;> intro impossible <;> cases impossible
      | cons mode modes =>
          cases mode with
          | input =>
              simp only [resolveInputs, Option.map_eq_some_iff]
              constructor
              · rintro ⟨tail, found, rfl⟩
                exact .input ((ih _ _).mp found)
              · intro source
                cases source with
                | input rest => exact ⟨_, (ih _ _).mpr rest, rfl⟩
          | output =>
              simp only [resolveInputs, Option.map_eq_some_iff]
              constructor
              · rintro ⟨tail, found, rfl⟩
                exact .output ((ih _ _).mp found)
              · intro source
                cases source with
                | output rest => exact ⟨_, (ih _ _).mpr rest, rfl⟩

inductive ArgumentHolds : RelationArgMode → Subst → Atom → Atom → Subst → Prop where
  | input {initial : Subst} {schema value : Atom} (same : applySubst initial schema = value) :
      ArgumentHolds .input initial schema value initial
  | output {initial final : Subst} {schema value : Atom}
      (matched : SpaceSemantics.ValueMatch initial schema value final) :
      ArgumentHolds .output initial schema value final

inductive ArgumentsHold : Subst → List Atom → List Atom → List RelationArgMode → Subst → Prop where
  | nil {initial : Subst} : ArgumentsHold initial [] [] [] initial
  | cons {initial middle final : Subst} {schema value : Atom} {schemas values : List Atom}
      {mode : RelationArgMode} {modes : List RelationArgMode} :
      ArgumentHolds mode initial schema value middle →
      ArgumentsHold middle schemas values modes final →
      ArgumentsHold initial (schema :: schemas) (value :: values) (mode :: modes) final

def matchArguments (initial : Subst) :
    List Atom → List Atom → List RelationArgMode → Option Subst
  | [], [], [] => some initial
  | schema :: schemas, value :: values, .input :: modes =>
      if applySubst initial schema = value then matchArguments initial schemas values modes else none
  | schema :: schemas, value :: values, .output :: modes =>
      (SpaceSemantics.matchValue initial schema value).bind fun middle =>
        matchArguments middle schemas values modes
  | _, _, _ => none

@[simp] theorem matchArguments_exact (initial : Subst) (schemas values : List Atom)
    (modes : List RelationArgMode) (final : Subst) :
    matchArguments initial schemas values modes = some final ↔
      ArgumentsHold initial schemas values modes final := by
  induction schemas generalizing initial values modes with
  | nil =>
      cases values with
      | nil =>
          cases modes with
          | nil =>
              constructor
              · intro same; cases same; exact .nil
              · intro source; cases source; rfl
          | cons mode modes => constructor <;> intro impossible <;> cases impossible
      | cons value values =>
          cases modes <;> constructor <;> intro impossible <;> cases impossible
  | cons schema schemas ih =>
      cases values with
      | nil => constructor <;> intro impossible <;> cases impossible
      | cons value values =>
          cases modes with
          | nil => constructor <;> intro impossible <;> cases impossible
          | cons mode modes =>
              cases mode with
              | input =>
                  simp only [matchArguments]
                  constructor
                  · intro computed
                    split at computed
                    next same => exact .cons (.input same) ((ih _ _ _).mp computed)
                    next => contradiction
                  · intro source
                    cases source with
                    | cons head tail =>
                        cases head with
                        | input same => simp [same, (ih _ _ _).mpr tail]
              | output =>
                  simp only [matchArguments, Option.bind_eq_some_iff]
                  constructor
                  · rintro ⟨middle, matched, continued⟩
                    exact .cons (.output ((SpaceSemantics.matchValue_exact _ _ _ _).mp matched))
                      ((ih _ _ _).mp continued)
                  · intro source
                    cases source with
                    | cons head tail =>
                        cases head with
                        | output matched =>
                            exact ⟨_, SpaceSemantics.matchValue_complete matched, (ih _ _ _).mpr tail⟩

/-- Finite declarations and native responses are different source rules.
An unavailable native call supplies no constructor; an empty completed table
supplies no selected occurrence. No failure invents a successful query. -/
inductive QueryHolds (environment : Environment) (relation : String)
    (arguments : List Atom) (initial : Subst) : Origin → Subst → Prop where
  | relation {index : Nat} {values : List Atom} {final : Subst}
      (stored : environment.rows[index]? =
        some (.expression (.symbol "relation!" :: .symbol relation :: values)))
      (matched : SpaceSemantics.ValueMatch initial (.expression arguments) (.expression values) final) :
      QueryHolds environment relation arguments initial (.relation index) final
  | builtin {index : Nat} {values : List Atom} {final : Subst}
      (stored : environment.rows[index]? =
        some (.expression (.symbol "builtin!" :: .symbol relation :: values)))
      (matched : SpaceSemantics.ValueMatch initial (.expression arguments) (.expression values) final) :
      QueryHolds environment relation arguments initial (.builtin index) final
  | native {index : Nat} {signature : Signature} {resolved : List Pattern}
      {rows : List (List Pattern)} {values : List Atom} {final : Subst}
      (registered : relation ∈ environment.registration.dynamicRelations)
      (declared : signature? environment.registration relation arguments.length = some signature)
      (inputs : Inputs initial arguments signature.modes resolved)
      (source : environment.dynamic.Source relation resolved rows)
      (selected : rows[index]? = some (GroundData.encodeList values))
      (matched : ArgumentsHold initial arguments values signature.modes final) :
      QueryHolds environment relation arguments initial (.native index) final


/-- A native source proof records occurrence choices and its finite child
structure. This is proof syntax, not a Boolean definition of validity. -/
inductive Evidence where
  | firing (declaration : Nat) (premises : Evidence)
  | empty
  | cons (head tail : Evidence)
  | fresh
  | child (proof : Evidence)
  | query (origin : Origin)
  deriving Repr, DecidableEq

mutual
  inductive RootFiring (environment : Environment) : Evidence → Atom → Atom → Prop where
    | rule {index : Nat} {proof : Evidence} {left right subject target : Atom} {guards : List Atom}
        {initial final : Subst}
        (stored : ClauseAt environment.rows index left right guards)
        (matched : SpaceSemantics.ValueMatch [] left subject initial)
        (premises : PremisesHold environment proof guards initial final)
        (emitted : target = applySubst final right) :
        RootFiring environment (.firing index proof) subject target

  inductive PremiseHolds (environment : Environment) : Evidence → Atom → Subst → Subst → Prop where
    | fresh {name : String} {subject : Atom} {initial : Subst}
        (held : SourceGuardHolds initial (.freshness name subject)) :
        PremiseHolds environment .fresh
          (.expression [.symbol "fresh", .var name, subject]) initial initial
    | child {proof : Evidence} {source target result : Atom} {initial final : Subst}
        (fired : RootFiring environment proof (applySubst initial source) result)
        (matched : SpaceSemantics.ValueMatch initial target result final) :
        PremiseHolds environment (.child proof)
          (.expression [.symbol "==", source, target]) initial final
    | query {relation : String} {arguments : List Atom} {initial final : Subst} {origin : Origin}
        (ordinary : relation ≠ "fresh") (directed : relation ≠ "==")
        (queried : QueryHolds environment relation arguments initial origin final) :
        PremiseHolds environment (.query origin)
          (.expression (.symbol relation :: arguments)) initial final

  inductive PremisesHold (environment : Environment) : Evidence → List Atom → Subst → Subst → Prop where
    | nil {initial : Subst} : PremisesHold environment .empty [] initial initial
    | cons {head tail : Evidence} {guard : Atom} {guards : List Atom} {initial middle final : Subst}
        (held : PremiseHolds environment head guard initial middle)
        (rest : PremisesHold environment tail guards middle final) :
        PremisesHold environment (.cons head tail) (guard :: guards) initial final
end

/-- Derivability forgets the finite article, while the native judgment above
retains all declaration and query occurrence choices. -/
def Derives (environment : Environment) (subject target : Atom) : Prop :=
  ∃ evidence, RootFiring environment evidence subject target

/-- Guard-free ordinary source equations are a conservative part of this
conditional source calculus, with exactly the original matcher and body. -/
theorem unguarded_firing {environment : Environment} {index : Nat} {left right subject : Atom}
    {initial : Subst}
    (stored : environment.rows[index]? = some (.expression [.symbol "=", left, right]))
    (matched : SpaceSemantics.ValueMatch [] left subject initial) :
    RootFiring environment (.firing index .empty) subject (applySubst initial right) :=
  .rule ⟨_, stored, .equation _ _⟩ matched .nil rfl


/-- Callable preparation preserves the original evaluator's body and
assignment separately. Captured values and syntax-sensitive dispatch retain
their original evaluator roles. -/
inductive CallReady (environment : Environment) (head : String) (values : List Atom) :
    Evidence → Nat → Eval.Control → Prop where
  | guarded {prepared : PreparedClause} {final : Subst} {proof : Evidence}
      (selected : PreparedAt environment.rows head values prepared)
      (premises : PremisesHold environment proof prepared.guards prepared.bindings final) :
      CallReady environment head values (.firing prepared.declarationIndex proof)
        prepared.declarationIndex (.evaluate final prepared.equation.body)

/-- Actual old equation-clause selection is preserved at the exact evaluator
continuation. This says nothing about overriding primitive priority. -/
theorem original_clause_continuation {program : SpaceSemantics.Program} {head : String}
    {values : List Atom} {equation : SpaceSemantics.Equation} {bindings : Subst}
    (member : equation ∈ program.equations) (named : equation.head = head)
    (matched : SpaceSemantics.ValueMatches [] equation.arguments values bindings) :
    Eval.Control.evaluate bindings equation.body ∈ Eval.clauses program head values := by
  apply List.mem_filterMap.mpr
  refine ⟨equation, member, ?_⟩
  simp only [named, ↓reduceIte, SpaceSemantics.matchValues_complete matched, Option.map_some]

/-- A guard-free original callable equation has precisely the original
prepared body continuation in the extended profile. -/
theorem original_equation_ready {environment : Environment} {index : Nat} {head : String}
    {arguments values : List Atom} {body : Atom} {bindings : Subst}
    (stored : environment.rows[index]? =
      some (.expression [.symbol "=", .expression (.symbol head :: arguments), body]))
    (matched : SpaceSemantics.ValueMatch [] (.expression arguments) (.expression values) bindings) :
    CallReady environment head values (.firing index .empty) index (.evaluate bindings body) :=
  .guarded (.matched ⟨_, stored, .equation _ _ _⟩ rfl matched) .nil


/-- Captured values are returned by the actual evaluator; their expression
syntax is not restarted as a fresh program. -/
theorem captured_variable_returns (program : SpaceSemantics.Program) (configuration : Eval.Configuration)
    (bindings : Subst) (name : String) (value : Atom)
    (current : configuration.control = .evaluate bindings (.var name))
    (captured : bindings.lookup name = some value) :
    Eval.step program configuration = some {configuration with control := .returned [value]} := by
  have original := Eval.transition_step (DeclarativeSpec.Transition.value_variable
    (program := program) current)
  simpa only [applySubst, captured, Option.getD_some] using original

/-- Re-evaluating an expression substituted for a captured variable changes
an actual machine step. Raw authored rewriting and evaluator continuations
therefore require an explicit comparison, even for a terminating source call. -/
theorem captured_restart_boundary (program : SpaceSemantics.Program) (configuration : Eval.Configuration)
    (bindings : Subst) (name head : String) (arguments : List Atom)
    (captured : bindings.lookup name = some (.expression (.symbol head :: arguments)))
    (notControl : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false)
    (callable : (Eval.ioHead head || StdLib.known head || program.equations.any (·.head == head)) = true) :
    (Eval.step program {configuration with control := .evaluate bindings (.var name)}).map
        (fun next => next.control) ≠
      (Eval.step program {configuration with control := .evaluate [] (.expression (.symbol head :: arguments))}).map (fun next => next.control) := by
  have first := captured_variable_returns program
    {configuration with control := .evaluate bindings (.var name)} bindings name _ rfl captured
  have second := Eval.transition_step (DeclarativeSpec.Transition.call_enter
    (source := {configuration with control := .evaluate [] (.expression (.symbol head :: arguments))})
    (program := program) rfl notControl callable)
  rw [first, second]
  simp only [Option.map_some]
  intro same
  cases same

end Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional



set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation (Program)

/-- Finite provided modules carry the original source commands and their
physical lines. The table is an explicit source input, not a file-system
oracle or an ambient unrestricted import implementation. -/
abbrev ProvidedModules := List (Atom × Program Atom)

/-- Module selection is first-match at the original physical table index.
Later duplicate names do not silently replace an already selected module. -/
inductive ModuleAt : ProvidedModules → Atom → Nat → Program Atom → Prop where
  | here (tail : ProvidedModules) (name : Atom) (commands : Program Atom) :
      ModuleAt ((name, commands) :: tail) name 0 commands
  | later {tail : ProvidedModules} {key name : Atom} {first commands : Program Atom}
      {index : Nat} (different : key ≠ name) (selected : ModuleAt tail name index commands) :
      ModuleAt ((key, first) :: tail) name (index + 1) commands

def providedModule? : ProvidedModules → Atom → Option (Nat × Program Atom)
  | [], _ => none
  | (key, commands) :: tail, name =>
      if key = name then some (0, commands)
      else (providedModule? tail name).map fun (index, selected) => (index + 1, selected)

@[simp] theorem providedModule?_exact (modules : ProvidedModules) (name : Atom)
    (index : Nat) (commands : Program Atom) :
    providedModule? modules name = some (index, commands) ↔ ModuleAt modules name index commands := by
  induction modules generalizing index with
  | nil =>
      constructor
      · intro absent; contradiction
      · intro selected; cases selected
  | cons entry tail ih =>
      obtain ⟨key, first⟩ := entry
      by_cases same : key = name
      · subst key
        simp only [providedModule?, ↓reduceIte, Option.some.injEq, Prod.mk.injEq]
        constructor
        · rintro ⟨indexSame, commandSame⟩
          subst index
          subst commands
          exact .here _ _ _
        · intro selected
          cases selected with
          | here => exact ⟨rfl, rfl⟩
          | later different _ => exact False.elim (different rfl)
      · simp only [providedModule?, same, ↓reduceIte, Option.map_eq_some_iff]
        constructor
        · rintro ⟨⟨actualIndex, actualCommands⟩, chosen, pairSame⟩
          cases pairSame
          exact .later same ((ih _).mp chosen)
        · intro selected
          cases selected with
          | here => exact False.elim (same rfl)
          | later _ selected => exact ⟨(_, commands), (ih _).mpr selected, rfl⟩

end Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands
